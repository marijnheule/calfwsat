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
#   TIMEOUT=3600  wall-clock cap per run in seconds (default: 3600; set empty
#                 for no cap). A run that hits the cap counts as unsolved and
#                 contributes 2*TIMEOUT to PAR-2.
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
TIMEOUT="${TIMEOUT-3600}"

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

# -------- aggregate: one config row, sweep-one leaderboard columns --------
# Columns match sweep-one.sh: config runs SAT TO PAR-2 mean_flips median_flips
# (only one config here = solver defaults, so the table has a single data row).
read RUNS NSAT NTO PAR2 MEAN_FLIPS MEDIAN_FLIPS < <(awk -F, -v to="${TIMEOUT:-0}" '
  NR==1 { next }
  { n++
    if ($2=="SAT") { sat++; sumt+=$4+0; f[fs++]=$3+0 }
    else           { unsolved++ }
  }
  END {
    par = (sumt + 2*to*unsolved)
    parv = n ? par/n : 0
    for (i=1;i<fs;i++){ k=f[i]; j=i-1; while(j>=0 && f[j]>k){f[j+1]=f[j];j--}; f[j+1]=k }
    if (fs>0) {
      for (i=0;i<fs;i++) mean+=f[i]; mean/=fs
      med = (fs%2) ? f[int(fs/2)] : (f[fs/2-1]+f[fs/2])/2.0
      mf=sprintf("%.0f",mean); mdf=sprintf("%.0f",med)
    } else { mf="-"; mdf="-" }
    printf "%d %d %d %.2f %s %s\n", n, sat, unsolved, parv, mf, mdf
  }
' "$CSV")

[ -n "$TIMEOUT" ] && TIMEOUT_DISP="${TIMEOUT}s per run" || TIMEOUT_DISP="none"

# Leaderboard table (plain) — the single config row.
SUMMARY="$OUT_DIR/summary.txt"
{
  printf '%-10s %5s %5s %5s %10s %12s %14s\n' \
    config runs SAT TO PAR-2 mean_flips median_flips
  printf '%-10s %5s %5s %5s %10s %12s %14s\n' \
    default "$RUNS" "$NSAT" "$NTO" "$PAR2" "$MEAN_FLIPS" "$MEDIAN_FLIPS"
} > "$SUMMARY"

# Plain-text email (metadata header + leaderboard), like sweep-one.sh.
TXT="$OUT_DIR/email.txt"
{
  echo "palsat default-settings run on $FORMULA"
  echo "  host:    $HOST"
  echo "  commit:  $COMMIT"
  echo "  date:    $DATE"
  echo "  threads: $THREADS per run"
  echo "  seeds:   $N  ($SEED0..$SEED_END)"
  echo "  timeout: $TIMEOUT_DISP"
  echo
  cat "$SUMMARY"
} > "$TXT"

# Markdown email (single-row table), like sweep-one.sh.
MD="$OUT_DIR/email.md"
{
  echo "## palsat default-settings run on \`$FORMULA\`"
  echo
  echo "- host: \`$HOST\`"
  echo "- commit: \`$COMMIT\`"
  echo "- date: $DATE"
  echo "- threads: $THREADS per run"
  echo "- seeds: $N ($SEED0..$SEED_END)"
  echo "- timeout: $TIMEOUT_DISP"
  echo
  echo "| config | runs | SAT | TO | PAR-2 | mean_flips | median_flips |"
  echo "|---|---:|---:|---:|---:|---:|---:|"
  printf "| %s | %s | %s | %s | %s | %s | %s |\n" \
    default "$RUNS" "$NSAT" "$NTO" "$PAR2" "$MEAN_FLIPS" "$MEDIAN_FLIPS"
} > "$MD"

echo
echo "==================== copy/paste for email (plain) ===================="
cat "$TXT"
echo
echo "==================== copy/paste for email (markdown) ================="
cat "$MD"
echo "======================================================================"
echo
echo "Files in ${OUT_DIR#$SCRIPT_DIR/}/:"
echo "  email.txt     — plain text, paste into email body"
echo "  email.md      — markdown, paste into email body"
echo "  summary.txt   — leaderboard (single config row)"
echo "  results.csv   — raw per-seed data (seed,result,flips,seconds)"
echo "  seed-*.log    — full palsat output per seed"
