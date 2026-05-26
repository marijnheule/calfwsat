#!/bin/sh
# Sweep palsat over ntil-30..40 and report wall time, best cost, shared-cache stats.
#
# Usage:
#   sh sweep.sh [seed] [timeout_sec] [threads] [first] [last]
#
# Defaults: seed=7 timeout=60 threads=8 first=30 last=40
#
# Logs are written to /tmp/palsat-sweep/ntil-N.log

set -u

SEED=${1:-7}
TIMEOUT_SEC=${2:-60}
THREADS=${3:-8}
FIRST=${4:-30}
LAST=${5:-40}

LOGDIR=/tmp/palsat-sweep
mkdir -p "$LOGDIR"
rm -f "$LOGDIR"/*.log witness.sol

printf "palsat sweep: seed=%s timeout=%ss threads=%s range=ntil-%s..%s\n\n" \
  "$SEED" "$TIMEOUT_SEC" "$THREADS" "$FIRST" "$LAST"

n=$FIRST
while [ "$n" -le "$LAST" ]; do
  inst="ntil-$n.knf"
  log="$LOGDIR/ntil-$n.log"
  rm -f witness.sol
  timeout "$TIMEOUT_SEC" ./solver/palsat -t "$THREADS" \
    --cutoff=2000 --maxtries=1000000 --card_compute=2 \
    "$inst" "$SEED" > "$log" 2>&1
  rc=$?

  st=$(grep -E "^s " "$log" | head -1)
  wall=$(grep "total wall clock" "$log" | head -1 | awk '{print $6}')
  used=$(grep "c shared cache: capacity" "$log" | head -1 | sed 's/.*used \([0-9]*\).*/\1/')
  ins=$(grep "c shared cache: inserts" "$log" | head -1 | sed 's/.*inserts \([0-9]*\).*/\1/')
  ham=$(grep "c shared cache: inserts" "$log" | head -1 | sed 's/.*ham-replaces \([0-9]*\).*/\1/')
  wor=$(grep "c shared cache: inserts" "$log" | head -1 | sed 's/.*worse-replaces \([0-9]*\).*/\1/')
  picks=$(grep "c shared cache: picks" "$log" | head -1 | sed 's/.*picks \([0-9]*\).*/\1/')
  best=$(grep "final worker" "$log" | sed 's/.*minimum of \([0-9]*\).*/\1/' | sort -n | head -1)

  verify=""
  if [ -f witness.sol ] && echo "$st" | grep -q SATISFIABLE; then
    verify=$(./check-sat "$inst" witness.sol 2>&1 | grep -E "VERIFIED|FAIL|NOT" | head -1 | sed 's/^c //')
  fi

  printf "ntil-%-2s rc=%d  %-22s  best=%-3s  wall=%-7s  used=%-4s  ins=%-5s  ham=%-6s  worse=%-5s  picks=%-6s  %s\n" \
    "$n" "$rc" "$st" "$best" "$wall" "$used" "$ins" "$ham" "$wor" "$picks" "$verify"

  n=$((n + 1))
done
