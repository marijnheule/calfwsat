#!/usr/bin/env bash
# repeat-one.sh
#
# Run palsat with default options on a single formula N times (seeds 1..N),
# sequentially, with a per-run wall-clock timeout. Each palsat invocation
# uses the binary's full default thread pool (i.e. saturates the machine);
# runs are NOT overlapped.
#
# Usage:
#   bash repeat-one.sh <formula.knf> <timeout_sec> <N>
#
# Example:
#   bash repeat-one.sh ntil-45.knf 900 100
#
# Tunables (env vars):
#   PALSAT      path to palsat binary           (default ./solver/palsat)
#   THREADS     palsat -t N override            (default unset = use palsat's compiled default)
#
# Output:
#   bench-results/<basename>-repeat-<timestamp>/
#     seed-NNN.log    per-run palsat stdout
#     rows.txt        seed exitcode wall (raw per-run data)
#     summary.txt     SAT/TO counts, PAR-2, mean+median wall and flips
#
# Solver options: ALL DEFAULTS. The binary's compiled-in defaults are used.

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

# -------- setup --------
[ -x "$PALSAT" ] || { echo "error: palsat not executable at $PALSAT" >&2; exit 2; }
BASE="$(basename "$FORMULA" .knf)"; BASE="${BASE%.cnf}"
TS="$(date +%Y%m%d-%H%M%S)"
OUT_DIR="$SCRIPT_DIR/bench-results/${BASE}-repeat-${TS}"
mkdir -p "$OUT_DIR"
ROWS="$OUT_DIR/rows.txt"
: >"$ROWS"

echo "repeat-one: $FORMULA"
echo "  N:        $N (sequential)"
echo "  timeout:  ${TIMEOUT_SEC}s per run"
if [ -n "${THREADS:-}" ]; then echo "  threads:  $THREADS (override via -t)"; fi
echo "  palsat:   $PALSAT"
echo "  out:      $OUT_DIR"
echo

# -------- timeout binary detection --------
TIMEOUT_BIN=""
if command -v timeout  >/dev/null 2>&1; then TIMEOUT_BIN=timeout;
elif command -v gtimeout >/dev/null 2>&1; then TIMEOUT_BIN=gtimeout;
else echo "warning: no GNU timeout found; runs will not be killed at $TIMEOUT_SEC s" >&2; fi

# -------- portable monotonic seconds --------
now() { python3 -c 'import time;print(time.time())' 2>/dev/null || date +%s; }

# -------- build palsat argv --------
PALSAT_ARGS=()
if [ -n "${THREADS:-}" ]; then PALSAT_ARGS+=(-t "$THREADS"); fi

# -------- sequential loop --------
seed=1
while [ "$seed" -le "$N" ]; do
  log="$OUT_DIR/seed-${seed}.log"
  t0=$(now)
  if [ -n "$TIMEOUT_BIN" ]; then
    "$TIMEOUT_BIN" -k 5 "$TIMEOUT_SEC" "$PALSAT" ${PALSAT_ARGS[@]+"${PALSAT_ARGS[@]}"} "$FORMULA" "$seed" >"$log" 2>&1
  else
    "$PALSAT" ${PALSAT_ARGS[@]+"${PALSAT_ARGS[@]}"} "$FORMULA" "$seed" >"$log" 2>&1
  fi
  ec=$?
  t1=$(now)
  wall=$(awk -v a="$t0" -v b="$t1" 'BEGIN { printf "%.3f", b-a }')
  printf "%s %s %s\n" "$seed" "$ec" "$wall" >>"$ROWS"
  printf "  seed=%-5s exit=%-3d wall=%ss\n" "$seed" "$ec" "$wall"
  seed=$(( seed + 1 ))
done

# -------- summary --------
SUMMARY="$OUT_DIR/summary.txt"
awk -v N="$N" -v TO="$TIMEOUT_SEC" -v OUT="$OUT_DIR" '
BEGIN { nsat=0; nto=0; nother=0; par2=0; sumwall_sat=0; sumflips_sat=0 }
{
  seed=$1; ec=$2; wall=$3+0
  sat=0; flips=0
  cmd="grep -E \"^s SATISFIABLE|total flips\" " OUT "/seed-" seed ".log"
  while ((cmd | getline line) > 0) {
    if (line ~ /^s SATISFIABLE/) sat=1
    else if (line ~ /total flips/) { gsub(/.*total flips +/, "", line); flips=line+0 }
  }
  close(cmd)
  if (sat==1) {
    nsat++; sumwall_sat += wall; sumflips_sat += flips
    walls[nsat] = wall; flipsa[nsat] = flips
    par2 += wall
  } else if (ec==124 || ec==137 || wall >= TO-1) {
    nto++; par2 += 2*TO
  } else {
    nother++; par2 += 2*TO
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
}
' "$ROWS" >"$SUMMARY"

echo
echo "==================== summary ===================="
cat "$SUMMARY"
echo
echo "Per-seed logs:  $OUT_DIR/seed-*.log"
echo "Raw rows:       $ROWS  (seed exitcode wall)"
echo "Summary:        $SUMMARY"
