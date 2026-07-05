#!/usr/bin/env bash
# sweep-one.sh
#
# Run a standard configuration sweep on a single benchmark and print a
# result table suitable for sharing via email.
#
# Usage:
#   bash sweep-one.sh <formula> [seed-start]
#
# The optional 2nd arg sets the start of the seed range; the sweep always uses
# SEED_COUNT (200) consecutive seeds. Omit it to use the baked-in default start.
# (The SEEDS env var still overrides the whole list and takes precedence.)
#
# Example:
#   bash sweep-one.sh ntil-40.knf          # seeds <default-start> .. +199
#   bash sweep-one.sh ntil-40.knf 6000     # seeds 6000 .. 6199
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
#
# Seed range: SEED_COUNT consecutive seeds starting at SEED_START. The start
# comes from the optional 2nd positional arg if given, else SEED_START_DEFAULT.
# An explicit SEEDS env var overrides the whole list (highest precedence).
SEED_START_DEFAULT=5701
SEED_COUNT=200
if [ -n "${2:-}" ] && ! [[ "$2" =~ ^[0-9]+$ ]]; then
  echo "error: seed-start (2nd arg) must be a positive integer, got '$2'" >&2; exit 2
fi
SEED_START="${2:-$SEED_START_DEFAULT}"
SEEDS_DEFAULT="${SEEDS:-$(seq "$SEED_START" "$((SEED_START + SEED_COUNT - 1))" | paste -sd, -)}"
TIMEOUT_DEFAULT="${TIMEOUT:-3600}"
THREADS_DEFAULT="${THREADS:-8}"
# Empty by default: do NOT override the solver's compiled cutoff default.
# A run differs from solver defaults only by what each config row sets.
# Override deliberately with e.g. CUTOFF=20000 bash sweep-one.sh <formula>.
CUTOFF_DEFAULT="${CUTOFF:-}"
CONFIGS_REL="${CONFIGS:-bench/configs-dynmul-scan.tsv}"
# ------------------------------------------------------------------

FORMULA="${1:?usage: $0 <formula.knf> [seed-start]}"
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

# Compiled defaults of the weight-transfer knobs (same provenance assumption).
# floor/slope define the linear transfer w = slope/1000 * (source_weight - floor);
# clsselectp is the random-source-shortcut probability (percent). Surfaced
# because these set the baseline every config row is measured against.
# (grep allows optional spaces after the comma, e.g. "clsselectp, 0".)
FLOOR_DEFAULT="$(grep -oE 'floor, *[0-9]+' "$SCRIPT_DIR/solver/options.h" 2>/dev/null | head -1 | grep -oE '[0-9]+')"
FLOOR_DEFAULT="${FLOOR_DEFAULT:-?}"
SLOPE_DEFAULT="$(grep -oE 'slope, *[0-9]+' "$SCRIPT_DIR/solver/options.h" 2>/dev/null | head -1 | grep -oE '[0-9]+')"
SLOPE_DEFAULT="${SLOPE_DEFAULT:-?}"
CLSSELECTP_DEFAULT="$(grep -oE 'clsselectp, *[0-9]+' "$SCRIPT_DIR/solver/options.h" 2>/dev/null | head -1 | grep -oE '[0-9]+')"
CLSSELECTP_DEFAULT="${CLSSELECTP_DEFAULT:-?}"
# inject is the additive-weighting knob (sub-N transfers inject a full N onto the
# sink): N=1 is the post-0cd8527 default and changes solver behavior vs N=0, so
# it is surfaced for provenance (mixing inject=0 and inject=1 runs is invalid).
INJECT_DEFAULT="$(grep -oE 'inject, *[0-9]+' "$SCRIPT_DIR/solver/options.h" 2>/dev/null | head -1 | grep -oE '[0-9]+')"
INJECT_DEFAULT="${INJECT_DEFAULT:-?}"
# min_gain snaps |flip_gain| < min_gain/1000 to 0 (near-zero-gain suppression).
# Surfaced for provenance; this sweep varies it, per-config rows set --min-gain=.
MIN_GAIN_DEFAULT="$(grep -oE 'min_gain, *[0-9]+' "$SCRIPT_DIR/solver/options.h" 2>/dev/null | head -1 | grep -oE '[0-9]+')"
MIN_GAIN_DEFAULT="${MIN_GAIN_DEFAULT:-?}"

echo "sweep-one: $FORMULA"
echo "  configs:  $CONFIGS"
echo "  commit:   $COMMIT"
echo "  seeds:    $SEEDS_DEFAULT"
echo "  timeout:  ${TIMEOUT_DEFAULT}s"
echo "  threads:  $THREADS_DEFAULT per palsat"
echo "  cutoff:   ${CUTOFF_DEFAULT:-(solver default; per-config rows can set --cutoff=)}"
echo "  oldestsource: $OLDESTSOURCE_DEFAULT (compiled default; per-config rows can set --oldestsource=)"
echo "  floor:    $FLOOR_DEFAULT  slope: $SLOPE_DEFAULT  clsselectp: $CLSSELECTP_DEFAULT  inject: $INJECT_DEFAULT  min_gain: $MIN_GAIN_DEFAULT (compiled defaults; per-config rows can override)"
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
  echo "  floor: $FLOOR_DEFAULT  slope: $SLOPE_DEFAULT  clsselectp: $CLSSELECTP_DEFAULT  inject: $INJECT_DEFAULT  min_gain: $MIN_GAIN_DEFAULT (compiled defaults; per-config rows can override)"
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
  echo "- floor: $FLOOR_DEFAULT, slope: $SLOPE_DEFAULT, clsselectp: $CLSSELECTP_DEFAULT, inject: $INJECT_DEFAULT, min_gain: $MIN_GAIN_DEFAULT (compiled defaults; per-config rows can override)"
  echo
  echo "| config | runs | SAT | TO | PAR-2 | median_plen | median_flips | median_succ |"
  echo "|---|---:|---:|---:|---:|---:|---:|---:|"
  awk 'NR>1 {
    printf "| %s | %s | %s | %s | %s | %s | %s | %s |\n",
      $1, $2, $3, $4, $5, $6, $7, $8
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
