#!/usr/bin/env bash
# compare.sh
#
# Run palsat with the SAME default settings on multiple formulas, with
# the same seeds and timeout, and print a per-formula leaderboard
# (PAR-2 / SAT% / mean+median flips). Mirror of sweep-one.sh but
# parameterized over instances instead of configs.
#
# Usage:
#   bash compare.sh <formula1> <formula2> [<formula3> ...]
#
# Example:
#   bash compare.sh ntil-43.knf ntil-45.knf ntil-46.knf
#
# Tunables (env vars; defaults match sweep-one.sh):
#   SEEDS       comma-separated seeds        (default "1,2,...,100")
#   TIMEOUT     per-run wall timeout (s)     (default 900)
#   THREADS     palsat -t N                  (default 8)
#   CUTOFF      palsat --cutoff=N            (default 20000)
#   ARGS        extra palsat args to add on top of defaults (default "")
#
# Output: bench-results/compare-<timestamp>/
#   results.csv          raw per-run rows
#   per-formula.txt      one row per formula (PAR-2 ranked)
#   email.txt / .md      copy-pasteable tables

set -uo pipefail

if [ "$#" -lt 1 ]; then
  echo "usage: $0 <formula1> <formula2> [<formula3> ...]" >&2
  exit 2
fi

# -------- defaults --------
SEEDS_DEFAULT="${SEEDS:-$(seq 1 100 | paste -sd, -)}"
TIMEOUT_DEFAULT="${TIMEOUT:-900}"
THREADS_DEFAULT="${THREADS:-8}"
CUTOFF_DEFAULT="${CUTOFF:-20000}"
ARGS_DEFAULT="${ARGS:-}"

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
TIMESTAMP="$(date +%Y%m%d-%H%M%S)"
OUT_NAME="compare-${TIMESTAMP}"
OUT_DIR="$SCRIPT_DIR/bench-results/$OUT_NAME"
mkdir -p "$OUT_DIR"

# -------- collect & validate formulas --------
FORMULAS=()
for f in "$@"; do
  [ -r "$f" ] || { echo "error: cannot read formula '$f'" >&2; exit 2; }
  # store ABSOLUTE paths so bench-parallel.sh resolves them no matter where
  # it cd's to.
  if [[ "$f" = /* ]]; then
    FORMULAS+=("$f")
  else
    FORMULAS+=("$(cd "$(dirname "$f")" && pwd)/$(basename "$f")")
  fi
done

# -------- temp config + instances --------
CONFIGS_TMP="$OUT_DIR/configs.tsv"
{
  echo "# Single-config sweep across multiple formulas (compare.sh)."
  echo "# All formulas run with the same args -- one row, one config."
  echo "default	${ARGS_DEFAULT}"
} > "$CONFIGS_TMP"

INSTANCES_TMP="$OUT_DIR/instances.txt"
: > "$INSTANCES_TMP"
for f in "${FORMULAS[@]}"; do
  echo "$f" >> "$INSTANCES_TMP"
done

# -------- log header --------
echo "compare: $# formula(s)"
for f in "${FORMULAS[@]}"; do echo "  - $f"; done
echo "  seeds:    $SEEDS_DEFAULT"
echo "  timeout:  ${TIMEOUT_DEFAULT}s per run"
echo "  threads:  $THREADS_DEFAULT per palsat"
echo "  cutoff:   $CUTOFF_DEFAULT"
[ -n "$ARGS_DEFAULT" ] && echo "  args:     $ARGS_DEFAULT"
echo "  out:      $OUT_DIR"
echo

# -------- delegate --------
bash "$SCRIPT_DIR/bench-parallel.sh" \
  --timeout "$TIMEOUT_DEFAULT" \
  --threads "$THREADS_DEFAULT" \
  --cutoff "$CUTOFF_DEFAULT" \
  "$CONFIGS_TMP" \
  "$INSTANCES_TMP" \
  "$SEEDS_DEFAULT" \
  "$OUT_DIR"

CSV="$OUT_DIR/results.csv"
[ -r "$CSV" ] || { echo "error: results.csv not produced — see $OUT_DIR" >&2; exit 3; }

# -------- per-formula summary --------
# results.csv columns: config,instance,vars,seed,result,rc,wall,best,flips
PFT="$OUT_DIR/per-formula.txt"
awk -F, -v T="$TIMEOUT_DEFAULT" '
  NR==1 { next }
  { inst=$2; res=$5; wall=$7+0; flips=$9+0
    n[inst]++
    if (res == "SAT") s[inst]++
    par_sum[inst] += (res == "SAT" ? wall : 2*T)
    if (res == "SAT") {
      flist[inst] = flist[inst] " " flips
      wlist[inst] = wlist[inst] " " wall
    } }
  END {
    for (i in n) {
      ss = s[i] ? s[i] : 0; tt = n[i] - ss
      par2 = par_sum[i] / n[i]
      # mean+median of flips and wall, SAT-only
      nf = split(flist[i], fa, " "); m = 0
      for (k = 1; k <= nf; k++) if (fa[k] != "") { m++; fv[m] = fa[k] }
      for (k = 1; k <= m; k++) for (l = k+1; l <= m; l++)
        if (fv[k]+0 > fv[l]+0) { tmp = fv[k]; fv[k] = fv[l]; fv[l] = tmp }
      mean_f = 0; for (k = 1; k <= m; k++) mean_f += fv[k]; mean_f = m ? mean_f/m : 0
      median_f = m == 0 ? 0 : (m % 2 == 1 ? fv[(m+1)/2] : (fv[m/2] + fv[m/2+1]) / 2)

      nw = split(wlist[i], wa, " "); mw = 0
      for (k = 1; k <= nw; k++) if (wa[k] != "") { mw++; wv[mw] = wa[k] }
      for (k = 1; k <= mw; k++) for (l = k+1; l <= mw; l++)
        if (wv[k]+0 > wv[l]+0) { tmp = wv[k]; wv[k] = wv[l]; wv[l] = tmp }
      mean_w = 0; for (k = 1; k <= mw; k++) mean_w += wv[k]; mean_w = mw ? mean_w/mw : 0
      median_w = mw == 0 ? 0 : (mw % 2 == 1 ? wv[(mw+1)/2] : (wv[mw/2] + wv[mw/2+1]) / 2)

      printf "%-30s %6d %6d %6d %10.2f %10.2f %10.2f %16.0f %16.0f\n", \
        i, n[i], ss, tt, par2, mean_w, median_w, mean_f, median_f
      delete fv; delete wv
    } }
' "$CSV" | sort -k5 -n > "$PFT.body" 2>/dev/null

{
  printf "%-30s %6s %6s %6s %10s %10s %10s %16s %16s\n" \
    "formula" "runs" "SAT" "TO" "PAR-2" "mean_w" "median_w" "mean_flips" "median_flips"
  cat "$PFT.body" 2>/dev/null
} > "$PFT"
rm -f "$PFT.body"

# -------- emailable tables --------
HOST="$(uname -n)"
DATE="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
NSEEDS="$(echo "$SEEDS_DEFAULT" | tr ',' '\n' | wc -l | tr -d ' ')"

TXT="$OUT_DIR/email.txt"
{
  echo "palsat compare across $# formula(s)"
  echo "  host:    $HOST"
  echo "  date:    $DATE"
  echo "  seeds:   $NSEEDS  ($SEEDS_DEFAULT)"
  echo "  timeout: ${TIMEOUT_DEFAULT}s per run"
  echo "  args:    --cutoff=$CUTOFF_DEFAULT ${ARGS_DEFAULT}"
  echo
  cat "$PFT"
} > "$TXT"

MD="$OUT_DIR/email.md"
{
  echo "## palsat compare across $# formula(s)"
  echo
  echo "- host: \`$HOST\`"
  echo "- date: $DATE"
  echo "- seeds: $NSEEDS ($SEEDS_DEFAULT)"
  echo "- timeout: ${TIMEOUT_DEFAULT}s per run"
  echo "- args: \`--cutoff=$CUTOFF_DEFAULT ${ARGS_DEFAULT}\`"
  echo
  echo "| formula | runs | SAT | TO | PAR-2 | mean_w | median_w | mean_flips | median_flips |"
  echo "|---|---:|---:|---:|---:|---:|---:|---:|---:|"
  awk 'NR>1 {
    printf "| %s | %s | %s | %s | %s | %s | %s | %s | %s |\n",
      $1, $2, $3, $4, $5, $6, $7, $8, $9
  }' "$PFT"
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
echo "  per-formula.txt    — leaderboard (one row per formula)"
echo "  email.txt          — plain text, paste into email body"
echo "  email.md           — markdown, paste into email body"
echo "  results.csv        — raw per-run data"
echo "  report.txt         — bench-parallel.sh combined report"
