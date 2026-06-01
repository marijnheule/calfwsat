#!/usr/bin/env bash
# repeat-parallel.sh
#
# Run palsat N times on a single formula with default solver options, with
# each palsat invocation pinned to a fixed thread count (default 8) and
# up to PARALLEL concurrent runs (default auto = cores / threads).
#
# Same shape as sweep-one.sh but without the config matrix: it's a pure
# "same configuration, N seeds, in parallel" runner -- useful for
# SAT-rate/PAR-2 measurements where you want statistical power and you're
# willing to time-slice the box across many simultaneous palsats.
#
# Usage:
#   bash repeat-parallel.sh <formula.knf> <timeout_sec> <N>
#
# Example:
#   bash repeat-parallel.sh ntil-45.knf 20 1000
#
# Tunables (env vars):
#   PALSAT      path to palsat binary           (default ./solver/palsat)
#   THREADS     threads each palsat uses        (default 8)
#   PARALLEL    max concurrent palsat procs     (default auto: cores/THREADS)
#
# Output:
#   bench-results/<basename>-repeatp-<timestamp>/
#     <basename>.<seed>.log   per-run palsat stdout (with -v)
#     rows.txt                seed exitcode wall (raw per-run data)
#     summary.txt             SAT/TO counts, PAR-2, mean+median, and a
#                             1-second-bucket wall-time histogram.

set -uo pipefail

# -------- args --------
[ $# -eq 3 ] || { echo "usage: $0 <formula.knf> <timeout_sec> <N>" >&2; exit 2; }
FORMULA="$1"; TIMEOUT_SEC="$2"; N="$3"
[ -r "$FORMULA" ] || { echo "error: cannot read formula '$FORMULA'" >&2; exit 2; }
case "$TIMEOUT_SEC" in (*[!0-9]*|"") echo "timeout must be a positive integer" >&2; exit 2;; esac
case "$N" in (*[!0-9]*|"") echo "N must be a positive integer" >&2; exit 2;; esac
[ "$N" -ge 1 ] || { echo "N must be >= 1" >&2; exit 2; }

# -------- tunables --------
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PALSAT="${PALSAT:-$SCRIPT_DIR/solver/palsat}"
THREADS="${THREADS:-8}"

detect_physical_cores() {
  local n=
  if command -v lscpu >/dev/null 2>&1; then
    n=$(lscpu -p 2>/dev/null | awk -F, '!/^#/ {print $2","$3}' | sort -u | wc -l | tr -d ' ')
  fi
  if [ -z "$n" ] || [ "$n" -lt 1 ]; then
    n=$(sysctl -n hw.physicalcpu 2>/dev/null || true)
  fi
  if [ -z "$n" ] || [ "$n" -lt 1 ]; then
    n=$(nproc 2>/dev/null || echo 1)
  fi
  echo "$n"
}
if [ -z "${PARALLEL:-}" ]; then
  CORES=$(detect_physical_cores)
  PARALLEL=$(( CORES / THREADS ))
  [ "$PARALLEL" -lt 1 ] && PARALLEL=1
fi

# -------- setup --------
[ -x "$PALSAT" ] || { echo "error: palsat not executable at $PALSAT" >&2; exit 2; }
BASE="$(basename "$FORMULA" .knf)"; BASE="${BASE%.cnf}"
TS="$(date +%Y%m%d-%H%M%S)"
OUT_DIR="$SCRIPT_DIR/bench-results/${BASE}-repeatp-${TS}"
mkdir -p "$OUT_DIR"
ROWS="$OUT_DIR/rows.txt"
: >"$ROWS"

echo "repeat-parallel: $FORMULA"
echo "  N:         $N"
echo "  timeout:   ${TIMEOUT_SEC}s per run"
echo "  threads:   $THREADS per palsat"
echo "  parallel:  $PARALLEL concurrent palsat processes"
echo "  palsat:    $PALSAT"
echo "  out:       $OUT_DIR"
echo

# -------- timeout binary detection --------
TIMEOUT_BIN=""
if command -v timeout  >/dev/null 2>&1; then TIMEOUT_BIN=timeout;
elif command -v gtimeout >/dev/null 2>&1; then TIMEOUT_BIN=gtimeout;
else echo "warning: no GNU timeout found; runs will not be killed at $TIMEOUT_SEC s" >&2; fi

# -------- portable monotonic seconds --------
now() { python3 -c 'import time;print(time.time())' 2>/dev/null || date +%s; }

# -------- worker: one palsat run --------
run_one() {
  local seed="$1"
  local log="$OUT_DIR/${BASE}.${seed}.log"
  local t0 t1 wall ec
  t0=$(now)
  if [ -n "$TIMEOUT_BIN" ]; then
    "$TIMEOUT_BIN" -k 5 "$TIMEOUT_SEC" "$PALSAT" -v -t "$THREADS" "$FORMULA" "$seed" >"$log" 2>/dev/null
  else
    "$PALSAT" -v -t "$THREADS" "$FORMULA" "$seed" >"$log" 2>/dev/null
  fi
  ec=$?
  t1=$(now)
  wall=$(awk -v a="$t0" -v b="$t1" 'BEGIN { printf "%.3f", b-a }')
  printf "%s %s %s\n" "$seed" "$ec" "$wall" >>"$ROWS"
  printf "  seed=%-5s exit=%-3d wall=%ss\n" "$seed" "$ec" "$wall"
}

# -------- launch loop: keep at most $PARALLEL workers alive --------
seed=1
while [ "$seed" -le "$N" ]; do
  while [ "$(jobs -rp | wc -l | tr -d ' ')" -ge "$PARALLEL" ]; do
    wait -n 2>/dev/null || sleep 0.2
  done
  run_one "$seed" &
  seed=$(( seed + 1 ))
done
wait

# -------- summary --------
SUMMARY="$OUT_DIR/summary.txt"
awk -v N="$N" -v TO="$TIMEOUT_SEC" -v OUT="$OUT_DIR" -v BASE="$BASE" '
BEGIN {
  nsat=0; nto=0; nother=0; par2=0; sumwall_sat=0; sumflips_sat=0
  for (i = 0; i <= TO; i++) hist[i] = 0
}
{
  seed=$1; ec=$2; wall=$3+0
  sat=0; flips=0
  cmd="grep -E \"^s SATISFIABLE|total flips\" " OUT "/" BASE "." seed ".log"
  while ((cmd | getline line) > 0) {
    if (line ~ /^s SATISFIABLE/) sat=1
    else if (line ~ /total flips/) { gsub(/.*total flips +/, "", line); flips=line+0 }
  }
  close(cmd)
  if (sat==1) {
    nsat++; sumwall_sat += wall; sumflips_sat += flips
    walls[nsat] = wall; flipsa[nsat] = flips
    par2 += wall
    b = int(wall); if (b >= TO) b = TO
    hist[b]++
  } else if (ec==124 || ec==137 || wall >= TO-1) {
    nto++; par2 += 2*TO; hist[TO]++
  } else {
    nother++; par2 += 2*TO; hist[TO]++
  }
}
function median_of(arr, n,    sorted, i, j, t) {
  if (n==0) return 0
  for (i=1;i<=n;i++) sorted[i]=arr[i]
  for (i=1;i<n;i++) for (j=i+1;j<=n;j++) if (sorted[i]>sorted[j]) { t=sorted[i]; sorted[i]=sorted[j]; sorted[j]=t }
  if (n%2==1) return sorted[(n+1)/2]
  return (sorted[n/2] + sorted[n/2+1]) / 2.0
}
END {
  mw = (nsat>0 ? sumwall_sat/nsat : 0)
  mf = (nsat>0 ? sumflips_sat/nsat : 0)
  medw = median_of(walls, nsat)
  medf = median_of(flipsa, nsat)
  printf "runs=%d  SAT=%d (%.1f%%)  TO=%d  other=%d\n", N, nsat, 100.0*nsat/N, nto, nother
  printf "PAR-2 = %.2f s (lower is better; SAT=wall, TO=2*timeout)\n", par2/N
  printf "wall sec  (sat-only):  mean %.2f  median %.2f\n", mw, medw
  printf "flips     (sat-only):  mean %.0f  median %.0f\n", mf, medf

  hmax = 0
  for (i = 0; i <= TO; i++) if (hist[i] > hmax) hmax = hist[i]
  barwidth = 50
  printf "\nwall-time histogram (1s buckets; bar maxed at %d count):\n", hmax
  for (i = 0; i <= TO; i++) {
    label = sprintf("%3d-%-3d s", i, i+1)
    if (i == TO) label = sprintf("%3d+   s  (TO/other)", TO)
    n_in_bar = (hmax > 0 ? int((1.0 * hist[i] * barwidth) / hmax + 0.5) : 0)
    bar = ""
    for (k = 0; k < n_in_bar; k++) bar = bar "#"
    printf "  %-22s %5d  %s\n", label, hist[i], bar
  }
}
' "$ROWS" >"$SUMMARY"

echo
echo "==================== summary ===================="
cat "$SUMMARY"
echo
echo "Per-seed logs:  $OUT_DIR/${BASE}.*.log"
echo "Raw rows:       $ROWS  (seed exitcode wall)"
echo "Summary:        $SUMMARY"
