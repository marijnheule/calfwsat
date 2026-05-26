#!/usr/bin/env bash
# bench-aggregate.sh
#
# Rebuild the results.csv, summary.txt, per-instance.txt and report.txt for
# a bench-parallel.sh output directory from its per-run rows/ files.
#
# Use this when bench-parallel.sh died after collecting rows but before the
# aggregation step, or when you want to re-aggregate after manually editing
# rows.
#
# Usage:
#   bash bench-aggregate.sh <out_dir>
#
# Example:
#   bash bench-aggregate.sh bench-results/sweep4-on-40

set -uo pipefail

OUT_DIR="${1:?usage: $0 <out_dir>}"
ROW_DIR="$OUT_DIR/rows"
[ -d "$ROW_DIR" ] || { echo "error: $ROW_DIR not a directory" >&2; exit 2; }

CSV="$OUT_DIR/results.csv"
{
  echo "config,instance,vars,seed,result,rc,wall,best"
  ls "$ROW_DIR"/*.row 2>/dev/null | sort | while read -r f; do cat "$f"; done
} > "$CSV"

NROWS=$(($(wc -l < "$CSV") - 1))
echo "wrote $CSV ($NROWS data rows)"

# Try to infer the timeout from the largest non-SAT wall time, default 60.
TIMEOUT_SEC=$(awk -F, 'NR>1 && $5!="SAT" && $7+0>m{m=$7+0} END{print (m>0?int(m+0.5):60)}' "$CSV")
echo "inferred timeout: ${TIMEOUT_SEC}s"

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
echo "wrote $SUMMARY"

PER_INST="$OUT_DIR/per-instance.txt"
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
          ss = s[key] ? s[key] : 0
          mw = ss ? ws[key]/ss : 0
          printf "  %2d/%-2d  %8.2fs    ", ss, n[key], mw
        } else { printf "  %-22s", "-" }
      }
      printf "\n"
    }
  }
' "$CSV" > "$PER_INST"
echo "wrote $PER_INST"

REPORT="$OUT_DIR/report.txt"
{
  echo "palsat bench-parallel report (aggregated post-hoc by bench-aggregate.sh)"
  echo "======================================================================="
  echo
  echo "generated: $(date -u +%Y-%m-%dT%H:%M:%SZ)"
  echo "out_dir:   $OUT_DIR"
  echo "rows:      $NROWS"
  echo "timeout:   ${TIMEOUT_SEC}s (inferred)"
  echo
  echo "Leaderboard (sorted by PAR-2 ascending; lower = better)"
  echo "-------------------------------------------------------"
  cat "$SUMMARY"
  echo
  echo "Per-instance breakdown (cell = N_SAT/N_RUNS  mean_wall)"
  echo "-------------------------------------------------------"
  cat "$PER_INST"
} > "$REPORT"
echo "wrote $REPORT"

echo
echo "=== summary ==="
cat "$SUMMARY"
