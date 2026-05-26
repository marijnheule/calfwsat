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
    trap 'rm -f "$INSTANCES_FILE"' EXIT
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

# auto-detect parallelism
if [ -z "${MAX_PARALLEL:-}" ]; then
  CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 8)
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

# Mirror everything we print to a run.log inside out_dir so the full session
# is captured in the committable output directory.
RUN_LOG="$OUT_DIR/run.log"
: > "$RUN_LOG"
exec > >(tee -a "$RUN_LOG") 2>&1

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

  local st res wall best vars
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

  # Write atomically: write to tmp then rename.
  printf "%s,%s,%s,%s,%s,%s,%s,%s\n" \
    "$cname" "$inst_base" "${vars:-0}" "$seed" "$res" "$rc" "$wall" "${best:-}" > "${row}.tmp"
  mv -f "${row}.tmp" "$row"
}

# ---------- main launch loop with concurrency cap ----------
launched=0
declare -A PIDS=()

reap_dead() {
  local pid
  for pid in "${!PIDS[@]}"; do
    if ! kill -0 "$pid" 2>/dev/null; then
      unset 'PIDS[$pid]'
    fi
  done
}

for inst in "${INSTS[@]}"; do
  for seed in "${SEEDS[@]}"; do
    for k in $(seq 0 $((NCFG-1))); do
      cname="${CFG_NAMES[$k]}"
      cargs="${CFG_ARGS[$k]}"

      # block until under the parallelism cap
      while [ "${#PIDS[@]}" -ge "$MAX_PARALLEL" ]; do
        # wait for ANY job to exit (bash 4.3+)
        wait -n 2>/dev/null || true
        reap_dead
      done

      run_one "$cname" "$cargs" "$inst" "$seed" &
      PIDS[$!]=1
      launched=$((launched+1))

      if [ $((launched % 50)) -eq 0 ] || [ "$launched" -eq "$NTOTAL" ]; then
        printf "  launched %d / %d (in flight: %d) at %s\n" \
          "$launched" "$NTOTAL" "${#PIDS[@]}" "$(date -u +%H:%M:%SZ)"
      fi
    done
  done
done

# drain
echo "  all $NTOTAL launched; waiting for ${#PIDS[@]} in-flight to finish..."
wait
echo "  all runs complete at $(date -u +%Y-%m-%dT%H:%M:%SZ)"

# ---------- concatenate per-run rows into one CSV ----------
CSV="$OUT_DIR/results.csv"
{
  echo "config,instance,vars,seed,result,rc,wall,best"
  # sort by config then instance then seed for determinism
  ls "$ROW_DIR"/*.row 2>/dev/null | sort | while read -r f; do cat "$f"; done
} > "$CSV"

n_rows=$(($(wc -l < "$CSV") - 1))
echo "  wrote $CSV with $n_rows data rows"

# ---------- summary: PAR-2, mean & median walltime per config ----------
SUMMARY="$OUT_DIR/summary.txt"
awk -F, -v T="$TIMEOUT_SEC" '
  NR==1 { next }
  {
    cfg=$1; res=$5; wall=$7+0
    n[cfg]++
    if (res == "SAT") { s[cfg]++; ws[cfg] += wall; walls[cfg] = walls[cfg] " " wall }
    par_sum[cfg] += (res == "SAT" ? wall : 2*T)
  }
  END {
    for (c in n) {
      ss = s[c] ? s[c] : 0
      tt = n[c] - ss
      mean_w = ss ? ws[c]/ss : 0
      par2 = par_sum[c] / n[c]
      nw = split(walls[c], arr, " "); m = 0
      for (i = 1; i <= nw; i++) if (arr[i] != "") { m++; v[m] = arr[i] }
      for (i = 1; i <= m; i++)
        for (j = i+1; j <= m; j++)
          if (v[i]+0 > v[j]+0) { t = v[i]; v[i] = v[j]; v[j] = t }
      median = m == 0 ? 0 : (m % 2 == 1 ? v[(m+1)/2] : (v[m/2] + v[m/2+1])/2)
      printf "%-30s %6d %6d %6d %10.2f %10.2f %10.2f\n", \
        c, n[c], ss, tt, par2, mean_w, median
      delete v
    }
  }
' "$CSV" | sort -k5 -n > "$SUMMARY.body"
{
  printf "%-30s %6s %6s %6s %10s %10s %10s\n" \
    "config" "runs" "SAT" "TO" "PAR-2" "mean_w" "median_w"
  cat "$SUMMARY.body"
} > "$SUMMARY"
rm -f "$SUMMARY.body"

echo
echo "=== summary ==="
cat "$SUMMARY"

# ---------- per-instance breakdown ----------
PER_INST="$OUT_DIR/per-instance.txt"
awk -F, '
  NR==1 { next }
  {
    cfg=$1; inst=$2; res=$5; wall=$7+0
    key = cfg "/" inst
    n[key]++
    if (res == "SAT") { s[key]++; ws[key] += wall }
    cfgs[cfg]=1; insts[inst]=1
  }
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
      inst = ia[i]
      printf "%-15s", inst
      for (j=1; j<=nc; j++) {
        c = ca[j]; key = c "/" inst
        if (n[key] > 0) {
          ss = s[key] ? s[key] : 0
          mw = ss ? ws[key]/ss : 0
          printf "  %2d/%-2d  %8.2fs    ", ss, n[key], mw
        } else { printf "  %-22s", "-" }
      }
      printf "\n"
    }
  }
' "$CSV" > "$PER_INST"

echo
echo "=== per-instance ==="
cat "$PER_INST"

# ---------- self-contained committable report ----------
# This file is intended to be checked into the repo so results can be
# reviewed later (or by someone else) without needing the per-run logs.
REPORT="$OUT_DIR/report.txt"
{
  echo "palsat bench-parallel report"
  echo "============================"
  echo
  echo "generated: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "host:      $(uname -n) $(uname -s) $(uname -m) $(uname -r 2>/dev/null)"
  echo "cores:     $(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo unknown)"
  echo "palsat:    $PALSAT"
  if [ -x "$PALSAT" ]; then
    echo "version:   $("$PALSAT" --version 2>/dev/null | head -1 || echo unknown)"
  fi
  echo
  echo "Setup"
  echo "-----"
  echo "  configs file:   $CONFIGS_FILE  ($NCFG configs)"
  echo "  instances file: $INSTANCES_FILE  ($NINST instances)"
  echo "  seeds:          ${SEEDS[*]}  (n=$NSEEDS)"
  echo "  timeout/run:    ${TIMEOUT_SEC}s"
  echo "  threads/run:    $PER_RUN_THREADS"
  echo "  parallel:       $MAX_PARALLEL concurrent palsat (~$((MAX_PARALLEL*PER_RUN_THREADS)) cores)"
  echo "  cutoff:         $CUTOFF"
  echo "  total runs:     $NTOTAL"
  echo
  echo "Configs"
  echo "-------"
  printf "  %-30s %s\n" "name" "args"
  for k in $(seq 0 $((NCFG-1))); do
    printf "  %-30s %s\n" "${CFG_NAMES[$k]}" "${CFG_ARGS[$k]:-(none)}"
  done
  echo
  echo "Instances"
  echo "---------"
  for I in "${INSTS[@]}"; do
    V=$(grep -m1 "^p " "$I" 2>/dev/null | awk '{print $3}')
    printf "  %-30s  vars=%s\n" "$I" "${V:-?}"
  done
  echo
  echo "Leaderboard (sorted by PAR-2 ascending; lower = better)"
  echo "-------------------------------------------------------"
  cat "$SUMMARY"
  echo
  echo "Per-instance breakdown (cell = N_SAT/N_RUNS  mean_wall)"
  echo "-------------------------------------------------------"
  cat "$PER_INST"
  echo
  echo "Files in this directory"
  echo "-----------------------"
  echo "  report.txt           - this file"
  echo "  run.log              - full stdout of the bench-parallel script"
  echo "  results.csv          - raw per-run CSV (long format)"
  echo "  summary.txt          - per-config aggregate"
  echo "  per-instance.txt     - per-config x per-instance matrix"
  echo "  <config>/<inst>-<seed>.log - per-run palsat stdout"
  echo "  rows/                - per-run intermediate csv rows (idempotency)"
} > "$REPORT"

echo
echo "=== report.txt ==="
cat "$REPORT"
echo
echo "end: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
echo "outputs in: $OUT_DIR"
