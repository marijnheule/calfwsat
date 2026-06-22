#!/usr/bin/env bash
# run-seeds.sh
#
# Run palsat with the *default* solver settings on the full machine, once per
# seed, sequentially, and print a result table (similar in spirit to
# sweep-one.sh but a different shape: one config = solver defaults, full-core
# parallel per run, N seeds one after the other).
#
# Usage:
#   bash run-seeds.sh <formula.knf> <N>
#
# Example:
#   bash run-seeds.sh ntil-47.knf 20      # seeds 1..20, palsat -t 192 each
#
# Each run is:  palsat -t <THREADS> <formula> <seed>
# with NO other flags, so the solver's compiled defaults apply (cutoff=300000,
# maxtries unlimited, etc.). Seeds are 1..N (override start with SEED0=).
#
# Env overrides:
#   THREADS=192   worker threads per run (default: all cores)
#   SEED0=1       first seed (runs SEED0 .. SEED0+N-1)
#   TIMEOUT=      wall-clock cap per run in seconds (default: none). When set,
#                 a run that hits the cap counts as unsolved and contributes
#                 2*TIMEOUT to PAR-2.
#
# Output goes to bench-results/<base>-defaults-<timestamp>/ and a plain-text
# + markdown table is printed to stdout for copy/paste into email.

set -uo pipefail

# -------- inputs ----------
FORMULA="${1:?usage: $0 <formula.knf> <N>}"
N="${2:?usage: $0 <formula.knf> <N>}"
[ -r "$FORMULA" ] || { echo "error: cannot read formula '$FORMULA'" >&2; exit 2; }
case "$N" in (*[!0-9]*|"") echo "error: N must be a positive integer" >&2; exit 2;; esac
[ "$N" -ge 1 ] || { echo "error: N must be >= 1" >&2; exit 2; }

# -------- defaults (override via env) ----------
THREADS="${THREADS:-$( (nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 192) )}"
SEED0="${SEED0:-1}"
TIMEOUT="${TIMEOUT:-}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PALSAT="$SCRIPT_DIR/solver/palsat"
[ -x "$PALSAT" ] || { echo "error: palsat binary not found/executable at $PALSAT" >&2; exit 2; }

# Absolute formula path so palsat's CWD does not matter.
FORMULA_ABS="$(cd "$(dirname "$FORMULA")" && pwd)/$(basename "$FORMULA")"

BASE="$(basename "$FORMULA" .knf)"; BASE="${BASE%.cnf}"
TIMESTAMP="$(date +%Y%m%d-%H%M%S)"
OUT_DIR="$SCRIPT_DIR/bench-results/${BASE}-defaults-${TIMESTAMP}"
mkdir -p "$OUT_DIR"

# Git provenance (matches sweep-one.sh): mark -dirty if tracked files differ.
COMMIT="$(git -C "$SCRIPT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown)"
if [ "$COMMIT" != unknown ] && ! git -C "$SCRIPT_DIR" diff --quiet HEAD 2>/dev/null; then
  COMMIT="${COMMIT}-dirty"
fi

HOST="$(uname -n)"
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
SEED_END=$((SEED0 + N - 1))

echo "run-seeds: $FORMULA"
echo "  binary:   $PALSAT"
echo "  commit:   $COMMIT"
echo "  settings: solver defaults (no flags)"
echo "  threads:  $THREADS per run"
echo "  seeds:    $SEED0..$SEED_END  ($N runs, sequential)"
echo "  timeout:  ${TIMEOUT:-none}"
echo "  out:      ${OUT_DIR#$SCRIPT_DIR/}"
echo

CSV="$OUT_DIR/results.csv"
echo "seed,result,flips,seconds" > "$CSV"

printf '%-8s  %-10s  %14s  %10s\n' "seed" "result" "flips" "seconds"
printf '%-8s  %-10s  %14s  %10s\n' "----" "------" "-----" "-------"

for ((s = SEED0; s <= SEED_END; s++)); do
  LOG="$OUT_DIR/seed-${s}.log"
  if [ -n "$TIMEOUT" ]; then
    timeout "$TIMEOUT" "$PALSAT" -t "$THREADS" "$FORMULA_ABS" "$s" > "$LOG" 2>&1
    rc=$?
  else
    "$PALSAT" -t "$THREADS" "$FORMULA_ABS" "$s" > "$LOG" 2>&1
    rc=$?
  fi

  sline="$(grep -m1 '^s ' "$LOG" || true)"
  flips="$(grep -m1 'total flips' "$LOG" | awk '{print $NF}')"
  secs="$(grep -m1 'total wall clock time' "$LOG" | grep -oE '[0-9]+\.[0-9]+' | head -1)"
  [ -n "$flips" ] || flips="-"
  [ -n "$secs" ]  || secs="-"

  if [ "$rc" = 124 ]; then
    result="TIMEOUT"; secs="$TIMEOUT"
  elif echo "$sline" | grep -q SATISFIABLE; then
    result="SAT"
  else
    result="UNKNOWN"
  fi

  echo "$s,$result,$flips,$secs" >> "$CSV"
  printf '%-8s  %-10s  %14s  %10s\n' "$s" "$result" "$flips" "$secs"
done

# -------- aggregate --------
SUMMARY="$OUT_DIR/summary.txt"
{
  echo "palsat default-settings run on $FORMULA"
  echo "  host:    $HOST"
  echo "  commit:  $COMMIT"
  echo "  date:    $DATE"
  echo "  threads: $THREADS per run"
  echo "  seeds:   $N  ($SEED0..$SEED_END)"
  echo "  timeout: ${TIMEOUT:-none}"
  echo
  awk -F, -v to="${TIMEOUT:-0}" '
    NR==1 { next }
    {
      n++
      res=$2
      if (res=="SAT") { sat++; t[ts++]=$4+0; f[fs++]=$3+0; par+=$4+0; sumt+=$4+0; sumf+=$3+0 }
      else            { par += 2*to }
    }
    function med(arr, m,  c, i, j, key) {
      # insertion sort the first m elements of arr
      for (i=1;i<m;i++){ key=arr[i]; j=i-1; while(j>=0 && arr[j]>key){arr[j+1]=arr[j];j--}; arr[j+1]=key }
      if (m==0) return 0
      if (m%2) return arr[int(m/2)]
      return (arr[m/2-1]+arr[m/2])/2.0
    }
    END {
      printf "runs:          %d\n", n
      printf "solved (SAT):  %d / %d  (%.1f%%)\n", sat, n, n?100.0*sat/n:0
      if (sat>0) {
        printf "time   (s):    mean %.2f  median %.2f  min %.2f  max %.2f   [solved only]\n",
               sumt/sat, med(t,ts), tmin(t,ts), tmax(t,ts)
        printf "flips:         mean %.0f  median %.0f                       [solved only]\n",
               sumf/sat, med(f,fs)
      }
      if (to+0>0) printf "PAR-2 (s):     %.2f  (unsolved charged 2x timeout)\n", par/n
    }
    function tmin(a,m,  i,v){ v=a[0]; for(i=1;i<m;i++) if(a[i]<v)v=a[i]; return v }
    function tmax(a,m,  i,v){ v=a[0]; for(i=1;i<m;i++) if(a[i]>v)v=a[i]; return v }
  ' "$CSV"
} > "$SUMMARY"

# Markdown per-seed table for email.
MD="$OUT_DIR/email.md"
{
  echo "## palsat default-settings run on \`$FORMULA\`"
  echo
  echo "- host: \`$HOST\`"
  echo "- commit: \`$COMMIT\`"
  echo "- date: $DATE"
  echo "- threads: $THREADS per run"
  echo "- seeds: $N ($SEED0..$SEED_END)"
  echo "- timeout: ${TIMEOUT:-none}"
  echo
  echo "| seed | result | flips | seconds |"
  echo "|---:|---|---:|---:|"
  awk -F, 'NR>1 { printf "| %s | %s | %s | %s |\n", $1,$2,$3,$4 }' "$CSV"
  echo
  echo '```'
  cat "$SUMMARY"
  echo '```'
} > "$MD"

echo
echo "==================== summary ===================="
cat "$SUMMARY"
echo
echo "==================== markdown (copy/paste) ======"
cat "$MD"
echo "================================================="
echo
echo "Files in ${OUT_DIR#$SCRIPT_DIR/}/:"
echo "  results.csv   — per-seed raw data (seed,result,flips,seconds)"
echo "  summary.txt   — aggregate stats"
echo "  email.md      — markdown table + summary"
echo "  seed-*.log    — full palsat output per seed"
