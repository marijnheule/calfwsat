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
#   configs:   bench/configs-cutoff.tsv  (per-try flip cutoff sweep)
#   seeds:     1..100
#   timeout:   900s per run
#   threads:   8 per palsat invocation
#   parallel:  auto = cores / threads
#
# Output is written to bench-results/<basename>-<timestamp>/ and a plain-text
# + markdown table is also printed to stdout for copy/paste into email.

set -uo pipefail

# -------- defaults (edit here, or override via env vars) ----------
# Any of these can be overridden by setting an env var when invoking:
#   TIMEOUT=300 SEEDS="1,2,3" bash sweep-one.sh <formula>
SEEDS_DEFAULT="${SEEDS:-$(seq 3301 3500 | paste -sd, -)}"
TIMEOUT_DEFAULT="${TIMEOUT:-900}"
THREADS_DEFAULT="${THREADS:-8}"
# Empty by default: do NOT override the solver's compiled cutoff default.
# A run differs from solver defaults only by what each config row sets.
# Override deliberately with e.g. CUTOFF=20000 bash sweep-one.sh <formula>.
CUTOFF_DEFAULT="${CUTOFF:-}"
CONFIGS_REL="${CONFIGS:-bench/configs-relative-wtmul.tsv}"
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

# Git provenance: the binary under test should be built from this commit.
# Append "-dirty" if tracked files differ from HEAD (the binary may then not
# correspond to the recorded commit). Untracked files are ignored on purpose.
COMMIT="$(git -C "$SCRIPT_DIR" rev-parse --short HEAD 2>/dev/null || echo unknown)"
if [ "$COMMIT" != unknown ] && ! git -C "$SCRIPT_DIR" diff --quiet HEAD 2>/dev/null; then
  COMMIT="${COMMIT}-dirty"
fi

# Compiled default of --oldestsource, read from the source the binary should be
# built from (same provenance assumption as COMMIT). Surfaced in the log because
# it flips the whole source-selection path (default-on => deterministic LRU
# picker, randk forced 0). Individual config rows may still override it.
OLDESTSOURCE_DEFAULT="$(grep -oE 'oldestsource,[0-9]+' "$SCRIPT_DIR/solver/options.h" 2>/dev/null | head -1 | cut -d, -f2)"
OLDESTSOURCE_DEFAULT="${OLDESTSOURCE_DEFAULT:-?}"

echo "sweep-one: $FORMULA"
echo "  configs:  $CONFIGS"
echo "  commit:   $COMMIT"
echo "  seeds:    $SEEDS_DEFAULT"
echo "  timeout:  ${TIMEOUT_DEFAULT}s"
echo "  threads:  $THREADS_DEFAULT per palsat"
echo "  cutoff:   ${CUTOFF_DEFAULT:-(solver default; per-config rows can set --cutoff=)}"
echo "  oldestsource: $OLDESTSOURCE_DEFAULT (compiled default; per-config rows can set --oldestsource=)"
echo "  out:      bench-results/$OUT_NAME"
echo

# Delegate to bench-parallel.sh. Only pass --cutoff when explicitly set, so
# that by default the solver's own compiled cutoff applies.
CUTOFF_ARGS=()
[ -n "$CUTOFF_DEFAULT" ] && CUTOFF_ARGS=(--cutoff "$CUTOFF_DEFAULT")
bash "$SCRIPT_DIR/bench-parallel.sh" \
  --timeout "$TIMEOUT_DEFAULT" \
  --threads "$THREADS_DEFAULT" \
  ${CUTOFF_ARGS[@]+"${CUTOFF_ARGS[@]}"} \
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
  echo "  commit:  $COMMIT"
  echo "  date:    $DATE"
  echo "  seeds:   $NSEEDS  ($SEEDS_DEFAULT)"
  echo "  timeout: ${TIMEOUT_DEFAULT}s per run"
  echo "  oldestsource: $OLDESTSOURCE_DEFAULT (compiled default; per-config rows can override)"
  echo
  cat "$SUMMARY"
} > "$TXT"

# Markdown version (renders as a table in most email clients)
MD="$OUT_DIR/email.md"
{
  echo "## palsat sweep on \`$FORMULA\`"
  echo
  echo "- host: \`$HOST\`"
  echo "- commit: \`$COMMIT\`"
  echo "- date: $DATE"
  echo "- seeds: $NSEEDS ($SEEDS_DEFAULT)"
  echo "- timeout: ${TIMEOUT_DEFAULT}s per run"
  echo "- oldestsource: $OLDESTSOURCE_DEFAULT (compiled default; per-config rows can override)"
  echo
  echo "| config | runs | SAT | TO | PAR-2 | mean_flips | median_flips |"
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
