#!/usr/bin/env bash
# sweep-one.sh
#
# Run a standard configuration sweep on a single benchmark and print a
# result table suitable for sharing via email.
#
# Usage:
#   bash sweep-one.sh <formula>
#
# Example:
#   bash sweep-one.sh ntil-40.knf
#
# Hardcoded defaults (edit at top of script to change):
#   configs:   bench/configs-sweep4.tsv  (15 configs incl. no_cache + default)
#   seeds:     1,2,3,4,5
#   timeout:   60s per run
#   threads:   8 per palsat invocation
#   parallel:  auto = cores / threads
#
# Output is written to bench-results/<basename>-<timestamp>/ and a plain-text
# + markdown table is also printed to stdout for copy/paste into email.

set -uo pipefail

# -------- defaults (edit here, or override via env vars) ----------
# Any of these can be overridden by setting an env var when invoking:
#   TIMEOUT=300 SEEDS="1,2,3" bash sweep-one.sh <formula>
SEEDS_DEFAULT="${SEEDS:-$(seq 1 20 | paste -sd, -)}"
TIMEOUT_DEFAULT="${TIMEOUT:-900}"
THREADS_DEFAULT="${THREADS:-8}"
CUTOFF_DEFAULT="${CUTOFF:-20000}"
CONFIGS_REL="${CONFIGS:-bench/configs-pos.tsv}"
# ------------------------------------------------------------------

FORMULA="${1:?usage: $0 <formula.knf>}"
[ -r "$FORMULA" ] || { echo "error: cannot read formula '$FORMULA'" >&2; exit 2; }

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
CONFIGS="$SCRIPT_DIR/$CONFIGS_REL"
[ -r "$CONFIGS" ] || { echo "error: configs file $CONFIGS not found" >&2; exit 2; }

BASE="$(basename "$FORMULA" .knf)"
BASE="${BASE%.cnf}"   # strip .cnf if present
TIMESTAMP="$(date +%Y%m%d-%H%M%S)"
OUT_NAME="${BASE}-${TIMESTAMP}"

echo "sweep-one: $FORMULA"
echo "  configs:  $CONFIGS"
echo "  seeds:    $SEEDS_DEFAULT"
echo "  timeout:  ${TIMEOUT_DEFAULT}s"
echo "  threads:  $THREADS_DEFAULT per palsat"
echo "  cutoff:   $CUTOFF_DEFAULT (per-config can override via --cutoff= in args)"
echo "  out:      bench-results/$OUT_NAME"
echo

# Delegate to bench-parallel.sh
bash "$SCRIPT_DIR/bench-parallel.sh" \
  --timeout "$TIMEOUT_DEFAULT" \
  --threads "$THREADS_DEFAULT" \
  --cutoff "$CUTOFF_DEFAULT" \
  "$CONFIGS" \
  "$FORMULA" \
  "$SEEDS_DEFAULT" \
  "$OUT_NAME"

OUT_DIR="$SCRIPT_DIR/bench-results/$OUT_NAME"
SUMMARY="$OUT_DIR/summary.txt"
[ -r "$SUMMARY" ] || { echo "error: summary.txt was not produced — see $OUT_DIR" >&2; exit 3; }

# -------- emailable tables --------
HOST="$(uname -n)"
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
NSEEDS="$(echo "$SEEDS_DEFAULT" | tr ',' '\n' | wc -l | tr -d ' ')"

# Plain-text version (monospace email; same as summary.txt with a header)
TXT="$OUT_DIR/email.txt"
{
  echo "palsat sweep on $FORMULA"
  echo "  host:    $HOST"
  echo "  date:    $DATE"
  echo "  seeds:   $NSEEDS  ($SEEDS_DEFAULT)"
  echo "  timeout: ${TIMEOUT_DEFAULT}s per run"
  echo
  cat "$SUMMARY"
} > "$TXT"

# Markdown version (renders as a table in most email clients)
MD="$OUT_DIR/email.md"
{
  echo "## palsat sweep on \`$FORMULA\`"
  echo
  echo "- host: \`$HOST\`"
  echo "- date: $DATE"
  echo "- seeds: $NSEEDS ($SEEDS_DEFAULT)"
  echo "- timeout: ${TIMEOUT_DEFAULT}s per run"
  echo
  echo "| config | runs | SAT | TO | PAR-2 | mean_w | median_w |"
  echo "|---|---:|---:|---:|---:|---:|---:|"
  awk 'NR>1 {
    printf "| %s | %s | %s | %s | %s | %s | %s |\n",
      $1, $2, $3, $4, $5, $6, $7
  }' "$SUMMARY"
} > "$MD"

echo
echo "==================== copy/paste for email (plain) ===================="
cat "$TXT"
echo
echo "==================== copy/paste for email (markdown) ================="
cat "$MD"
echo "======================================================================"
echo
echo "Files in $OUT_DIR/:"
echo "  email.txt          — plain text, paste into email body"
echo "  email.md           — markdown, paste into email body"
echo "  summary.txt        — leaderboard (plain)"
echo "  results.csv        — raw per-run data"
echo "  per-instance.txt   — config-by-instance matrix"
echo "  run.log            — full stdout of the underlying bench-parallel.sh"
