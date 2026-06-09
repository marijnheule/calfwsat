#!/bin/sh
# Multi-config, multi-seed benchmark runner for palsat.
#
# Usage:
#   sh bench.sh <configs_file> <instances_file> <seeds_csv> <timeout_sec> <threads> <out_dir>
#
# configs_file: lines of "<name><TAB><args-passed-to-palsat>"
#               name must be a safe path component; args do NOT include
#               --cutoff/--maxtries/--card_compute or the instance/seed.
#               Example:
#                  default<TAB>
#                  no_cache<TAB>--no-shared-cache
#                  rank_warmup<TAB>--shared-cache-pick=rank --shared-cache-warmup=5
#
# instances_file: lines of instance file paths (relative to repo root)
# seeds_csv:    comma-separated list of seeds, e.g. "1,2,3,4,5"
# timeout_sec:  per-run timeout in seconds
# threads:      passed as palsat -t
# out_dir:      output dir (created if missing). results.csv + summary.txt written here.
#
# Writes:
#   <out_dir>/<config>/<instance_basename>-<seed>.log   per-run log
#   <out_dir>/results.csv                                long-format results
#   <out_dir>/summary.txt                                per-config aggregate

set -u

CONFIGS="$1"
INSTANCES="$2"
SEEDS="$3"
TIMEOUT_SEC="$4"
THREADS="$5"
OUT_DIR="$6"

mkdir -p "$OUT_DIR"
CSV="$OUT_DIR/results.csv"
SUMMARY="$OUT_DIR/summary.txt"

echo "config,instance,vars,seed,result,rc,wall,best,picks,ham_repl,worse_repl,used,capacity" > "$CSV"

NSEEDS=$(echo "$SEEDS" | tr ',' '\n' | wc -l | tr -d ' ')
NINST=$(grep -cv '^$' "$INSTANCES")
NCFG=$(grep -cv '^$' "$CONFIGS")
echo "bench: $NCFG configs x $NINST instances x $NSEEDS seeds x ${TIMEOUT_SEC}s = $((NCFG * NINST * NSEEDS)) runs, threads=$THREADS" | tee "$OUT_DIR/manifest.txt"
echo "started: $(date -u +%Y-%m-%dT%H:%M:%SZ)" | tee -a "$OUT_DIR/manifest.txt"

# Read configs into parallel arrays (name + args).
i=0
while IFS=$(printf '\t') read -r CNAME CARGS; do
  [ -z "$CNAME" ] && continue
  case "$CNAME" in '#'*) continue ;; esac
  i=$((i + 1))
  eval "CFGNAME_$i=\$CNAME"
  eval "CFGARGS_$i=\$CARGS"
done < "$CONFIGS"
NCFG=$i

# Outer loop: instance, seed, config (run all configs back-to-back on same
# instance+seed so any system load drift affects them similarly).
while read -r INST; do
  [ -z "$INST" ] && continue
  case "$INST" in '#'*) continue ;; esac
  INST_BASE=$(basename "$INST" .knf)
  VARS=$(grep -m1 "^p " "$INST" 2>/dev/null | awk '{print $3}')
  [ -z "$VARS" ] && VARS=0

  echo "$SEEDS" | tr ',' '\n' | while read -r SEED; do
    [ -z "$SEED" ] && continue

    c=1
    while [ "$c" -le "$NCFG" ]; do
      eval "CNAME=\$CFGNAME_$c"
      eval "CARGS=\$CFGARGS_$c"
      LOGDIR="$OUT_DIR/$CNAME"
      mkdir -p "$LOGDIR"
      LOG="$LOGDIR/$INST_BASE-$SEED.log"
      rm -f witness.sol

      START_NS=$(date +%s)
      # Pass only -t and the per-config args; everything else uses the
      # solver's compiled defaults, so a run differs from defaults only by $CARGS.
      # shellcheck disable=SC2086
      timeout "$TIMEOUT_SEC" ./solver/palsat -t "$THREADS" \
        $CARGS "$INST" "$SEED" > "$LOG" 2>&1
      RC=$?

      ST_LINE=$(grep -E "^s " "$LOG" | head -1)
      case "$ST_LINE" in
        *SATISFIABLE*) RESULT=SAT ;;
        *UNSATISFIABLE*) RESULT=UNSAT ;;
        *) RESULT=TO ;;
      esac
      WALL=$(grep "total wall clock" "$LOG" | sed -E 's/.*of ([0-9.]+) seconds.*/\1/' | head -1)
      [ -z "$WALL" ] && WALL=$TIMEOUT_SEC
      BEST=$(grep "final worker" "$LOG" | sed 's/.*minimum of \([0-9]*\).*/\1/' | sort -n | head -1)
      [ -z "$BEST" ] && BEST=
      PICKS=$(grep "c shared cache: picks" "$LOG" | head -1 | sed 's/.*picks \([0-9]*\).*/\1/')
      HAMR=$(grep "c shared cache: inserts" "$LOG" | head -1 | sed 's/.*ham-replaces \([0-9]*\).*/\1/')
      WORSER=$(grep "c shared cache: inserts" "$LOG" | head -1 | sed 's/.*worse-replaces \([0-9]*\).*/\1/')
      USED=$(grep "c shared cache: capacity" "$LOG" | head -1 | sed 's/.*used \([0-9]*\).*/\1/')
      CAP=$(grep "c shared cache: capacity" "$LOG" | head -1 | sed 's/.*capacity \([0-9]*\).*/\1/')
      # verify witness when SAT
      if [ "$RESULT" = SAT ] && [ -f witness.sol ]; then
        ./check-sat "$INST" witness.sol 2>&1 | grep -q "VERIFIED" || RESULT=SAT_BAD
      fi

      printf "%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s\n" \
        "$CNAME" "$INST_BASE" "$VARS" "$SEED" "$RESULT" "$RC" "$WALL" \
        "$BEST" "${PICKS:-}" "${HAMR:-}" "${WORSER:-}" "${USED:-}" "${CAP:-}" >> "$CSV"
      printf "  %-30s  %-10s  seed=%-3s  %-7s  wall=%-7s  best=%s\n" \
        "$CNAME" "$INST_BASE" "$SEED" "$RESULT" "${WALL}s" "${BEST:-?}"

      c=$((c + 1))
    done
  done
done < "$INSTANCES"

echo "finished: $(date -u +%Y-%m-%dT%H:%M:%SZ)" | tee -a "$OUT_DIR/manifest.txt"

# Summary: per config aggregate. PAR-2 = sum over runs of (wall if SAT, else 2*T) / N.
awk -F, -v T="$TIMEOUT_SEC" '
  NR == 1 { next }
  {
    cfg = $1; res = $5; wall = $7 + 0
    runs[cfg]++
    if (res == "SAT")        { sat[cfg]++;     wsum[cfg] += wall;    nsolved[cfg]++ }
    else if (res == "TO")    { to[cfg]++ }
    else if (res == "UNSAT") { unsat[cfg]++ }
    else                     { bad[cfg]++ }
    par_sum[cfg] += (res == "SAT" ? wall : 2 * T)
    if (res == "SAT") { walls[cfg] = walls[cfg] " " wall }
    if (wall > wmax[cfg]) wmax[cfg] = wall
  }
  END {
    printf "%-30s %5s %5s %5s %5s %5s %9s %9s %9s\n", \
      "config", "runs", "SAT", "TO", "BAD", "UNS", "PAR-2", "mean_w", "median_w"
    for (c in runs) {
      n = runs[c]; s = sat[c] ? sat[c] : 0
      mean_w = s ? wsum[c]/s : 0
      par2 = par_sum[c] / n
      # median of walls[c]
      nw = split(walls[c], arr, " ")
      # arr[1] is empty if walls began with space; sort properly
      m = 0
      for (i = 1; i <= nw; i++) if (arr[i] != "") {m++; vals[m] = arr[i]}
      median = 0
      if (m > 0) {
        # naive sort
        for (i = 1; i <= m; i++) for (j = i+1; j <= m; j++) if (vals[i]+0 > vals[j]+0) { tmp = vals[i]; vals[i] = vals[j]; vals[j] = tmp }
        if (m % 2 == 1) median = vals[(m+1)/2]; else median = (vals[m/2] + vals[m/2+1]) / 2
      }
      printf "%-30s %5d %5d %5d %5d %5d %9.2f %9.2f %9.2f\n", \
        c, n, s, (to[c]?to[c]:0), (bad[c]?bad[c]:0), (unsat[c]?unsat[c]:0), par2, mean_w, median
      delete vals
    }
  }
' "$CSV" | sort > "$SUMMARY"

echo ""
echo "=== summary ($SUMMARY) ==="
cat "$SUMMARY"

# Per-instance breakdown: rows=instances, cols=configs, cell=#SAT/N mean_wall.
PER_INST="$OUT_DIR/per-instance.txt"
awk -F, '
  NR == 1 { next }
  {
    cfg = $1; inst = $2; res = $5; wall = $7 + 0
    key = cfg "/" inst
    n[key]++
    if (res == "SAT") { s[key]++; ws[key] += wall }
    cfgs[cfg] = 1; insts[inst] = 1
  }
  END {
    nc = 0
    for (c in cfgs) { nc++; cfg_arr[nc] = c }
    for (i = 1; i <= nc; i++) for (j = i+1; j <= nc; j++)
      if (cfg_arr[i] > cfg_arr[j]) { t = cfg_arr[i]; cfg_arr[i] = cfg_arr[j]; cfg_arr[j] = t }
    ni = 0
    for (ii in insts) { ni++; inst_arr[ni] = ii }
    for (i = 1; i <= ni; i++) for (j = i+1; j <= ni; j++)
      if (inst_arr[i] > inst_arr[j]) { t = inst_arr[i]; inst_arr[i] = inst_arr[j]; inst_arr[j] = t }
    printf "%-15s", "instance"
    for (i = 1; i <= nc; i++) printf "  %-18s", cfg_arr[i]
    printf "\n"
    for (i = 1; i <= ni; i++) {
      inst = inst_arr[i]
      printf "%-15s", inst
      for (j = 1; j <= nc; j++) {
        cfg = cfg_arr[j]
        key = cfg "/" inst
        if (n[key] > 0) {
          ss = s[key] ? s[key] : 0
          mw = ss ? ws[key]/ss : 0
          printf "  %2d/%-2d %8.2fs    ", ss, n[key], mw
        } else {
          printf "  %-18s", "-"
        }
      }
      printf "\n"
    }
  }
' "$CSV" > "$PER_INST"
echo ""
echo "=== per-instance ($PER_INST) ==="
cat "$PER_INST"
echo ""
echo "raw: $CSV"
