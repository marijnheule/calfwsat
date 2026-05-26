# palsat Shared Assignment Cache — Tuning Report

## TL;DR

(Filled in at end.)

## Feature recap

palsat (parallel portfolio version of CaLFwSAT) workers historically only
shared a "done" flag. This change adds a process-wide shared cache of up to
N "good" starting assignments. At each restart cycle a worker:

1. Releases the cache slot it previously held.
2. Inserts its best-of-just-finished try (per insert/replacement policy).
3. Picks a new starting assignment by weighted-random selection over
   unreserved slots; reserves the chosen slot.

Reservations guarantee no two workers start from the same cached assignment
concurrently. The Hamming-distance threshold collapses near-duplicate
entries to keep the cache diverse.

## Knobs (CLI flags)

| flag | default | meaning |
|---|---|---|
| `--no-shared-cache` | off | disable feature entirely |
| `--shared-cache-size=N` | **256** | capacity (max slots) |
| `--shared-cache-hamming=PCT` | **5** | near-dup threshold (bits = PCT × V / 100) |
| `--shared-cache-pick=NAME` | linear | linear / rank / softmax / uniform / inv |
| `--shared-cache-softmax-temp=T_x10` | 10 | softmax temperature × 10 (10 = T=1) |
| `--shared-cache-replace=POLICY` | worse | full-cache: worse / always / never |
| `--shared-cache-ham-replace=POLICY` | eq | Hamming-hit: eq / strict / always |
| `--shared-cache-warmup=N` | **5** | per-worker: skip shared pick for first N restarts |
| `--shared-cache-explore=PCT` | 0 | chance to ignore weights and pick uniformly |
| `--shared-cache-insert=MODE` | always | always / improved (gate insert on strict improvement vs start) |

**Note:** the defaults shown in bold (256 / 5% / warmup=5) were promoted
from the original baseline (1024 / 1% / warmup=0) after the partial sweep1
showed `combo_loose` consistently faster on ntil-35/36. The original
baseline numbers below were measured with the OLD defaults; the new
defaults still need to be re-baselined.

## Experimental setup

* Machine: `(record here)`
* Compiler: gcc/clang `(record)`
* palsat: `-t 8 --cutoff=2000 --maxtries=1000000 --card_compute=2`
* Per-run wall-clock timeout: 60 s
* Metric: PAR-2 (timeout = 2× T). Lower is better.
* Instances: `ntil-N.knf` for N=30..40 (and 41..50 for stress).

## Baseline: cache OFF vs default ON

5 seeds × 11 instances × 60 s.

| config | runs | SAT | TO | PAR-2 | mean wall (solved) | median wall (solved) |
|---|---|---|---|---|---|---|
| no_cache | 55 | 47 | 8 | 22.03 | 5.36s | 1.58s |
| default | 55 | 52 | 3 | **13.38** | 7.23s | 2.02s |

**Shared cache reduces PAR-2 by 39%** at the default settings. Per-instance
breakdown showed the cache wins clearly on the hardest cases (ntil-37 and
ntil-39: 4/5 vs 1/5 SAT), is roughly tied on easy cases, and loses one
specific easy case (ntil-31 — 4× slower than no_cache).

## Sweep 1: knob exploration

(Filled in after sweep1 completes.)

## Best configurations

(Filled in.)

## Stress test on ntil-41..50

(Filled in.)

## Recommendations

(Filled in.)

## Open questions / future work

* ntil-31 anomaly: investigate why shared cache is 4× slower than no_cache.
* "Anti-clustering" weight scheme: penalize recently-picked slots to
  diversify worker basins.
* Per-worker "self bias": let a worker that is making progress prefer
  its own basin rather than getting pulled to the cache leader.
* MaxSAT cost dimension: currently rank by `yals_minimum` (#unsat hard
  constraints). For pure-MaxSAT, ranking by soft-cost may be more useful.

## Raw data

* Baseline: `/tmp/bench-baseline/`
* Sweep1: `/tmp/bench-sweep1/`
* Sweep2 (focused): `/tmp/bench-sweep2/`
* Stress 41-50: `/tmp/bench-stress/`
