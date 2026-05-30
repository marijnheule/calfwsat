#!/usr/bin/env bash
# bench-parallel.sh
#
# Parameter-sweep runner designed for large-core machines (128+ cores).
#
# The existing bench.sh runs one palsat at a time. On a 192-core machine that
# leaves 184 cores idle. This runner launches a *matrix* of (config, instance,
# seed) palsat invocations in parallel, each using PER_RUN_THREADS internally,
# with at most PARALLEL concurrent processes. Total CPU usage saturates at
# roughly PARALLEL * PER_RUN_THREADS cores.
#
# Usage:
#   bash bench-parallel.sh [options] <configs_file> <instances_file> <seeds_csv> <out_dir>
#
# Options:
#   --timeout SEC      per-run wall-clock timeout    (default 60)
#   --threads N        threads each palsat uses      (default 8)
#   --parallel N       max concurrent palsat procs   (default auto: cores/threads)
#   --palsat PATH      path to palsat binary         (default ./solver/palsat)
#   --cutoff N         passed to palsat as --cutoff= (default 2000)
#   --no-skip-existing redo runs even if a row exists (default: skip existing)
#   -h, --help         show this help
#
# Positional arguments:
#   configs_file       TSV: "<name><TAB><palsat args>" per line; # = comment
#   instances          EITHER one instance path (foo.knf) for single-benchmark
#                      mode OR a file listing one instance path per line for
#                      multi-instance mode. Detected by .knf suffix.
#   seeds_csv          comma-separated seeds, e.g. "1,2,3,4,5"
#   out_dir            output directory (created if missing)
#
# Outputs:
#   <out_dir>/<config>/<inst>-<seed>.log    per-run log (full palsat stdout)
#   <out_dir>/rows/<cfg>__<inst>__<seed>.row  per-run csv row (idempotent)
#   <out_dir>/results.csv                   concatenated csv (header included)
#   <out_dir>/summary.txt                   per-config aggregate, sorted by PAR-2
#
# Idempotency:
#   Re-running with the same out_dir skips runs whose .row file already exists.
#   This means an interrupted sweep can be resumed by just re-invoking. To
#   force a full re-run, delete out_dir first (or pass --no-skip-existing).
#
# Tuning the parallelism on a 192-core machine:
#   The "right" balance depends on whether palsat scales linearly to high
#   thread counts on your workload (usually it does not past 16-32 threads,
#   because the SLS algorithm is mostly serial per worker). Suggested:
#     --threads 8   --parallel 24    (~192 cores, 24 data points in flight)
#     --threads 16  --parallel 12    (192 cores, fewer/faster runs)
#     --threads 4   --parallel 48    (192 cores, many parallel data points)
#   I'd default to threads=8 parallel=24 for sweeps; smaller threads-per-run
#   gives more data points per wall-second.

set -uo pipefail

# ---------- defaults ----------
PALSAT=./solver/palsat
PER_RUN_THREADS=8
MAX_PARALLEL=
TIMEOUT_SEC=60
CUTOFF=2000
SKIP_EXISTING=1

# ---------- arg parsing ----------
usage() { sed -n '1,/^set -uo/p' "$0" | sed -n '2,/^# Tuning/p' | sed -n '/^# Usage:/,/^# Tuning/p' | sed 's/^# \{0,1\}//' >&2; }

while [ $# -gt 0 ]; do
  case "$1" in
    --timeout)            TIMEOUT_SEC="$2"; shift 2 ;;
    --threads)            PER_RUN_THREADS="$2"; shift 2 ;;
    --parallel)           MAX_PARALLEL="$2"; shift 2 ;;
    --palsat)             PALSAT="$2"; shift 2 ;;
    --cutoff)             CUTOFF="$2"; shift 2 ;;
    --no-skip-existing)   SKIP_EXISTING=0; shift ;;
    -h|--help)            usage; exit 0 ;;
    --)                   shift; break ;;
    -*)                   echo "unknown option: $1" >&2; usage; exit 2 ;;
    *)                    break ;;
  esac
done

if [ "$#" -ne 4 ]; then
  echo "error: expected 4 positional arguments, got $#" >&2
  usage
  exit 2
fi

CONFIGS_FILE="$1"
INSTANCES_ARG="$2"
SEEDS_CSV="$3"
OUT_DIR="$4"

# Single-benchmark mode: if the instances arg ends in .knf, treat it as one
# instance path. Otherwise it's a file listing instances (one per line).
case "$INSTANCES_ARG" in
  *.knf|*.knf.gz|*.knf.bz2|*.knf.xz|*.cnf|*.cnf.gz|*.cnf.bz2|*.cnf.xz|*.wknf|*.wcnf)
    [ -r "$INSTANCES_ARG" ] || { echo "error: cannot read instance $INSTANCES_ARG" >&2; exit 2; }
    # synthesize a one-line instances file in a scratch tempdir
    INSTANCES_FILE=$(mktemp -t bp-instances.XXXXXX)
    echo "$INSTANCES_ARG" > "$INSTANCES_FILE"
    # (cleanup of this temp file is registered later in the combined
    #  EXIT/INT/TERM/HUP trap that also performs aggregation.)
    ;;
  *)
    INSTANCES_FILE="$INSTANCES_ARG"
    ;;
esac

# Repo-relative committable location. If out_dir is just a name (no slashes),
# place it under bench-results/ in the repo root next to this script.
case "$OUT_DIR" in
  /*|./*|../*) : ;;  # absolute or explicit relative -> use as-is
  *)
    SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
    OUT_DIR="$SCRIPT_DIR/bench-results/$OUT_DIR"
    ;;
esac

# auto-detect parallelism. Prefer PHYSICAL cores so we don't oversubscribe
# via SMT/hyperthreads (palsat's weight transfer is memory-bandwidth sensitive and rarely
# benefits from SMT). Fallback chain: lscpu (Linux) -> sysctl (macOS) -> nproc.
detect_physical_cores() {
  local n=
  # Linux: lscpu -p produces lines like "cpu,core,socket,..."; unique
  # (core,socket) tuples = physical cores.
  if command -v lscpu >/dev/null 2>&1; then
    n=$(lscpu -p=Core,Socket 2>/dev/null | grep -v '^#' | sort -u | wc -l | tr -d ' ')
    [ -n "$n" ] && [ "$n" -gt 0 ] && { echo "$n"; return; }
  fi
  # macOS: sysctl reports physical separately.
  if command -v sysctl >/dev/null 2>&1; then
    n=$(sysctl -n hw.physicalcpu 2>/dev/null)
    [ -n "$n" ] && [ "$n" -gt 0 ] && { echo "$n"; return; }
  fi
  # /proc/cpuinfo: count unique (physical id, core id) tuples.
  if [ -r /proc/cpuinfo ]; then
    n=$(awk '/^physical id/{p=$NF} /^core id/{print p","$NF}' /proc/cpuinfo \
          | sort -u | wc -l | tr -d ' ')
    [ -n "$n" ] && [ "$n" -gt 0 ] && { echo "$n"; return; }
  fi
  # Last resort: logical cores.
  n=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 8)
  echo "$n"
}

if [ -z "${MAX_PARALLEL:-}" ]; then
  CORES=$(detect_physical_cores)
  MAX_PARALLEL=$(( CORES / PER_RUN_THREADS ))
  [ "$MAX_PARALLEL" -lt 1 ] && MAX_PARALLEL=1
fi

# sanity
if [ ! -x "$PALSAT" ]; then
  echo "error: palsat binary not found or not executable at: $PALSAT" >&2
  echo "  (build with: cd solver && ./configure.sh && make)" >&2
  exit 2
fi
for f in "$CONFIGS_FILE" "$INSTANCES_FILE"; do
  [ -r "$f" ] || { echo "error: cannot read $f" >&2; exit 2; }
done

mkdir -p "$OUT_DIR/rows"
ROW_DIR="$OUT_DIR/rows"

# Mirror everything we print to a run.log inside out_dir.
RUN_LOG="$OUT_DIR/run.log"
: > "$RUN_LOG"
exec > >(tee -a "$RUN_LOG") 2>&1

# ---------- aggregation: defined early, run from EXIT trap ----------
# Defined as a function and triggered via trap EXIT so that even if the
# script gets killed (SIGHUP from terminal disconnect, SIGTERM, etc.) the
# CSV/summary/report still get written from whatever rows are on disk.
# Re-running the script later re-fires the trap; output files are
# overwritten idempotently.
do_aggregate() {
  # Don't error out if files are missing; this trap may run very early.
  set +u
  local CSV="$OUT_DIR/results.csv"
  local SUMMARY="$OUT_DIR/summary.txt"
  local PER_INST="$OUT_DIR/per-instance.txt"
  local REPORT="$OUT_DIR/report.txt"

  # If there are no row files yet, nothing to aggregate.
  if ! ls "$ROW_DIR"/*.row >/dev/null 2>&1; then
    return 0
  fi

  {
    echo "config,instance,vars,seed,result,rc,wall,best,flips"
    ls "$ROW_DIR"/*.row 2>/dev/null | sort | while read -r f; do cat "$f"; done
  } > "$CSV"
  local nrows=$(($(wc -l < "$CSV") - 1))

  # Summary columns: PAR-2 (from wall) plus mean/median flips over ALL runs.
  awk -F, -v T="$TIMEOUT_SEC" '
    NR==1 { next }
    { cfg=$1; res=$5; wall=$7+0; flips=$9+0
      n[cfg]++
      if (res == "SAT") s[cfg]++
      par_sum[cfg] += (res == "SAT" ? wall : 2*T)
      fsum[cfg] += flips
      flist[cfg] = flist[cfg] " " flips }
    END {
      for (c in n) {
        ss = s[c] ? s[c] : 0; tt = n[c] - ss
        par2 = par_sum[c] / n[c]
        mean_f = n[c] ? fsum[c]/n[c] : 0
        nf = split(flist[c], arr, " "); m = 0
        for (i = 1; i <= nf; i++) if (arr[i] != "") { m++; v[m] = arr[i] }
        for (i = 1; i <= m; i++) for (j = i+1; j <= m; j++)
          if (v[i]+0 > v[j]+0) { tmp = v[i]; v[i] = v[j]; v[j] = tmp }
        median_f = m == 0 ? 0 : (m % 2 == 1 ? v[(m+1)/2] : (v[m/2] + v[m/2+1])/2)
        printf "%-30s %6d %6d %6d %10.2f %16.0f %16.0f\n", \
          c, n[c], ss, tt, par2, mean_f, median_f
        delete v
      } }
  ' "$CSV" | sort -k5 -n > "$SUMMARY.body" 2>/dev/null
  {
    printf "%-30s %6s %6s %6s %10s %16s %16s\n" \
      "config" "runs" "SAT" "TO" "PAR-2" "mean_flips" "median_flips"
    cat "$SUMMARY.body" 2>/dev/null
  } > "$SUMMARY"
  rm -f "$SUMMARY.body"

  awk -F, '
    NR==1 { next }
    { cfg=$1; inst=$2; res=$5; wall=$7+0
      key = cfg "/" inst; n[key]++
      if (res == "SAT") { s[key]++; ws[key] += wall }
      cfgs[cfg]=1; insts[inst]=1 }
    END {
      nc=0; for (c in cfgs) { nc++; ca[nc]=c }
      for (i=1; i<=nc; i++) for (j=i+1; j<=nc; j++)
        if (ca[i] > ca[j]) { t=ca[i]; ca[i]=ca[j]; ca[j]=t }
      ni=0; for (ii in insts) { ni++; ia[ni]=ii }
      for (i=1; i<=ni; i++) for (j=i+1; j<=ni; j++)
        if (ia[i] > ia[j]) { t=ia[i]; ia[i]=ia[j]; ia[j]=t }
      printf "%-15s", "instance"
      for (i=1; i<=nc; i++) printf "  %-22s", ca[i]
      printf "\n"
      for (i=1; i<=ni; i++) {
        inst = ia[i]; printf "%-15s", inst
        for (j=1; j<=nc; j++) {
          c = ca[j]; key = c "/" inst
          if (n[key] > 0) {
            ss = s[key] ? s[key] : 0; mw = ss ? ws[key]/ss : 0
            printf "  %2d/%-2d  %8.2fs    ", ss, n[key], mw
          } else { printf "  %-22s", "-" }
        }
        printf "\n" } }
  ' "$CSV" > "$PER_INST" 2>/dev/null

  {
    echo "palsat bench-parallel report"
    echo "============================"
    echo
    echo "generated:  $(date -u +%Y-%m-%dT%H:%M:%SZ)"
    echo "out_dir:    $OUT_DIR"
    echo "rows:       $nrows"
    echo "timeout:    ${TIMEOUT_SEC}s"
    echo
    echo "Leaderboard (sorted by PAR-2 ascending; lower = better)"
    echo "-------------------------------------------------------"
    cat "$SUMMARY" 2>/dev/null
    echo
    echo "Per-instance breakdown (cell = N_SAT/N_RUNS  mean_wall)"
    echo "-------------------------------------------------------"
    cat "$PER_INST" 2>/dev/null
  } > "$REPORT"

  echo
  echo "=== aggregation done (trap EXIT): $nrows rows -> $CSV, summary, report ==="
}

# Combine with the cleanup trap for the temp instances file (if any).
_INSTANCES_TMP="${INSTANCES_FILE:-}"
case "${INSTANCES_ARG:-}" in
  *.knf|*.knf.gz|*.knf.bz2|*.knf.xz|*.cnf|*.cnf.gz|*.cnf.bz2|*.cnf.xz|*.wknf|*.wcnf)
    ;;  # _INSTANCES_TMP is the synthesized temp file
  *) _INSTANCES_TMP="" ;;
esac
trap '
  do_aggregate
  [ -n "$_INSTANCES_TMP" ] && [ -f "$_INSTANCES_TMP" ] && rm -f "$_INSTANCES_TMP"
' EXIT INT TERM HUP

# ---------- parse configs into parallel arrays ----------
CFG_NAMES=()
CFG_ARGS=()
while IFS=$'\t' read -r N A || [ -n "${N:-}" ]; do
  [ -z "${N:-}" ] && continue
  case "$N" in '#'*) continue ;; esac
  CFG_NAMES+=("$N")
  CFG_ARGS+=("${A:-}")
done < "$CONFIGS_FILE"
NCFG=${#CFG_NAMES[@]}

# ---------- parse instances ----------
INSTS=()
while read -r I || [ -n "${I:-}" ]; do
  [ -z "${I:-}" ] && continue
  case "$I" in '#'*) continue ;; esac
  INSTS+=("$I")
done < "$INSTANCES_FILE"
NINST=${#INSTS[@]}

# ---------- parse seeds ----------
IFS=',' read -ra SEEDS <<< "$SEEDS_CSV"
NSEEDS=${#SEEDS[@]}

NTOTAL=$((NCFG * NINST * NSEEDS))

cat <<EOF
bench-parallel:
  configs:      $NCFG
  instances:    $NINST
  seeds:        $NSEEDS  (${SEEDS[*]})
  total runs:   $NTOTAL
  timeout:      ${TIMEOUT_SEC}s per run
  threads/run:  $PER_RUN_THREADS
  parallel:     $MAX_PARALLEL  (~$((MAX_PARALLEL*PER_RUN_THREADS)) cores in use)
  cutoff:       $CUTOFF
  palsat:       $PALSAT
  out_dir:      $OUT_DIR
  skip_existing $SKIP_EXISTING
  start:        $(date -u +%Y-%m-%dT%H:%M:%SZ)

EOF

# ---------- the per-job worker ----------
# Runs one (config, instance, seed) combo and writes a CSV row.
run_one() {
  local cname="$1" cargs="$2" inst="$3" seed="$4"
  local inst_base log_dir log row
  inst_base=$(basename "$inst" .knf)
  log_dir="$OUT_DIR/$cname"
  log="$log_dir/${inst_base}-${seed}.log"
  row="$ROW_DIR/${cname}__${inst_base}__${seed}.row"

  if [ "$SKIP_EXISTING" -eq 1 ] && [ -s "$row" ]; then
    return 0
  fi
  mkdir -p "$log_dir"
  rm -f "$log" "$row"

  # shellcheck disable=SC2086
  timeout "$TIMEOUT_SEC" "$PALSAT" -t "$PER_RUN_THREADS" \
    --cutoff="$CUTOFF" --maxtries=1000000 --card_compute=2 \
    $cargs "$inst" "$seed" > "$log" 2>&1
  local rc=$?

  local st res wall best vars flips
  st=$(grep -E "^s " "$log" | head -1)
  case "$st" in
    *SATISFIABLE*)   res=SAT ;;
    *UNSATISFIABLE*) res=UNSAT ;;
    *)               res=TO ;;
  esac
  wall=$(grep "total wall clock" "$log" | sed -E 's/.*of ([0-9.]+) seconds.*/\1/' | head -1)
  [ -z "$wall" ] && wall=$TIMEOUT_SEC
  best=$(grep "final worker" "$log" | sed 's/.*minimum of \([0-9]*\).*/\1/' | sort -n | head -1)
  vars=$(grep -m1 "^p " "$inst" 2>/dev/null | awk '{print $3}')
  flips=$(grep "total flips" "$log" | sed -E 's/.*total flips ([0-9]+).*/\1/' | head -1)
  [ -z "$flips" ] && flips=0

  # Write atomically: write to tmp then rename.
  printf "%s,%s,%s,%s,%s,%s,%s,%s,%s\n" \
    "$cname" "$inst_base" "${vars:-0}" "$seed" "$res" "$rc" "$wall" "${best:-}" "$flips" > "${row}.tmp"
  mv -f "${row}.tmp" "$row"
}

# ---------- main launch loop with concurrency cap ----------
# Plain indexed array of background pids — works in bash 3.2+ (no -A needed).
launched=0
RUNNING=()

reap_dead() {
  local pid; local NEW=()
  if [ "${#RUNNING[@]}" -gt 0 ]; then
    for pid in "${RUNNING[@]}"; do
      if kill -0 "$pid" 2>/dev/null; then NEW+=("$pid"); fi
    done
  fi
  if [ "${#NEW[@]}" -gt 0 ]; then RUNNING=("${NEW[@]}"); else RUNNING=(); fi
}

for inst in "${INSTS[@]}"; do
  for seed in "${SEEDS[@]}"; do
    for k in $(seq 0 $((NCFG-1))); do
      cname="${CFG_NAMES[$k]}"
      cargs="${CFG_ARGS[$k]}"

      # block until under the parallelism cap
      while [ "${#RUNNING[@]}" -ge "$MAX_PARALLEL" ]; do
        # bash 4.3+: wait for any one job; bash 3.2 fallback: wait for first.
        if ! wait -n 2>/dev/null; then
          [ "${#RUNNING[@]}" -gt 0 ] && wait "${RUNNING[0]}" 2>/dev/null
        fi
        reap_dead
      done

      run_one "$cname" "$cargs" "$inst" "$seed" &
      RUNNING+=("$!")
      launched=$((launched+1))

      if [ $((launched % 50)) -eq 0 ] || [ "$launched" -eq "$NTOTAL" ]; then
        printf "  launched %d / %d (in flight: %d) at %s\n" \
          "$launched" "$NTOTAL" "${#RUNNING[@]}" "$(date -u +%H:%M:%SZ)"
      fi
    done
  done
done

# drain. IMPORTANT: wait *only* for the tracked palsat pids, not for the
# tee subprocess from `exec > >(tee ...)`. A bare `wait` blocks on tee's
# pipe (which is still open because the script is still running), causing
# the script to hang at the end and requiring a manual Ctrl-C.
echo "  all $NTOTAL launched; waiting for in-flight to finish..."
if [ "${#RUNNING[@]}" -gt 0 ]; then
  for _pid in "${RUNNING[@]}"; do
    wait "$_pid" 2>/dev/null || true
  done
fi
echo "  all runs complete at $(date -u +%Y-%m-%dT%H:%M:%SZ)"

# NOTE: aggregation (CSV + summary + per-instance + report) is handled by
# the EXIT trap (do_aggregate) so it runs even if the script is killed.
echo "  triggering aggregation via EXIT trap..."

# Trap handles aggregation on exit. Just print a final marker.
echo "end: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "outputs in: $OUT_DIR"
