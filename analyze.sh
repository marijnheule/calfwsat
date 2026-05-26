#!/bin/sh
# Per-instance breakdown of a bench results.csv.
# Usage: sh analyze.sh <results.csv>

set -u
CSV="$1"

awk -F, '
  NR == 1 { next }
  {
    cfg = $1; inst = $2; seed = $4; res = $5; wall = $7 + 0
    key = cfg "/" inst
    n[key]++
    if (res == "SAT") { s[key]++; ws[key] += wall }
    if (wall > wmax[key]) wmax[key] = wall
    # capture config and instance separately
    cfgs[cfg] = 1
    insts[inst] = 1
  }
  END {
    # print one row per instance, columns per config (mean wall + #sat/seeds)
    # First print header
    nc = 0
    for (c in cfgs) { nc++; cfg_arr[nc] = c }
    # alpha sort configs
    for (i = 1; i <= nc; i++) for (j = i+1; j <= nc; j++)
      if (cfg_arr[i] > cfg_arr[j]) { t = cfg_arr[i]; cfg_arr[i] = cfg_arr[j]; cfg_arr[j] = t }
    ni = 0
    for (ii in insts) { ni++; inst_arr[ni] = ii }
    for (i = 1; i <= ni; i++) for (j = i+1; j <= ni; j++)
      if (inst_arr[i] > inst_arr[j]) { t = inst_arr[i]; inst_arr[i] = inst_arr[j]; inst_arr[j] = t }

    printf "%-15s", "instance"
    for (i = 1; i <= nc; i++) printf "  %-20s", cfg_arr[i]
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
          printf "  %2d/%-2d  %6.2fs       ", ss, n[key], mw
        } else {
          printf "  %-20s", "-"
        }
      }
      printf "\n"
    }
  }
' "$CSV"
