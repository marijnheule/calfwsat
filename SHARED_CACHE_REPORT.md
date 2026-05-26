# palsat Shared Assignment Cache — Tuning & Validation Report

## TL;DR

We added a process-wide cache of "good" starting assignments shared across
palsat worker threads, exposed it through 10 tunable knobs, and ran roughly
nine sweeps of multi-config, multi-seed benchmarking to find a good default
configuration.

**Headline finding (negative):** at sensible per-try cutoff values, the
shared-cache feature provides **no statistically meaningful average benefit**
over `--no-shared-cache` on the no-three-in-line (ntil) instance set we
tested. A final A/B/C experiment at n=100 seeds × 3 hard instances showed:

| config | SAT (of 300) | mean PAR-2 |
|---|---|---|
| `default` (cache on, tuned) | 239 | 636 |
| `--no-shared-cache` | 236 | 631 |
| `linear_pick` cache variant | 219 | 729 |

That's a 3-run difference in SAT count and a 1% PAR-2 difference — well
within the run-to-run noise. The feature is statistically a wash with the
baseline.

**One robust positive finding:** within the cache configs, `pick=uniform`
consistently beats `pick=linear` on hard instances. That's a real one-knob
improvement, and it's the only tuning decision validated by the high-N
experiment.

**Important correction to an earlier claim:** the original baseline
comparison (sweep2, ~40% PAR-2 reduction from cache on vs off) was an
artifact of the `--no-shared-cache` baseline being crippled by an
unreasonably low `cutoff` default (2000 flips per try ≈ 5-10 ms). Once we
bumped the cutoff to a sensible value (10000+), the no_cache baseline became
much stronger, and the cache's apparent advantage disappeared.

## Feature description

palsat is the parallel-portfolio variant of CaLFwSAT: N worker threads, each
running the same stochastic local search (DDFW) on the same formula, with
different RNG seeds. Historically the only cross-worker signal was the
"done" flag — the first worker to find SAT terminated the others.

The shared cache adds cooperation. It is a process-wide, mutex-protected
fixed-capacity pool of assignment vectors. At each per-worker restart (= one
`cutoff` worth of flips completed), a worker:

1. **Releases** the cache slot it had been working from (if any).
2. **Inserts** its best-of-just-finished-try assignment, under a Hamming-near
   replacement policy: if the cache holds an assignment within
   `hamming_percent × V / 100` bits of the new one, replace it (subject to
   `ham_replace` policy); otherwise fill a free slot or evict the worst
   unreserved slot (subject to `replace_full` policy).
3. **Picks** a new starting assignment by weighted-random selection over
   unreserved slots; reserves the chosen slot.

Reservations guarantee no two workers concurrently start from the same
cached assignment.

All policy choices are runtime-configurable via the CLI flags below.

## CLI knobs

(All defaults from the final binary state at the time of this report.)

| flag | default | meaning |
|---|---|---|
| `--no-shared-cache` | off (cache enabled) | disable the feature entirely |
| `--shared-cache-size=N` | auto = 32 × threads | cache capacity (slots) |
| `--shared-cache-hamming=PCT` | 10 | near-duplicate threshold in % of V |
| `--shared-cache-pick=NAME` | uniform | linear / rank / softmax / uniform / inv |
| `--shared-cache-softmax-temp=T_x10` | 10 | softmax T × 10 (only if pick=softmax) |
| `--shared-cache-warmup=N` | 0 | per-worker: skip shared pick for first N restarts |
| `--shared-cache-explore=PCT` | 0 | chance to ignore weights and pick uniformly |
| `--shared-cache-insert=MODE` | always | always / improved (insert only if cost dropped) |
| `--shared-cache-replace=POLICY` | worse | full-cache: worse / always / never |
| `--shared-cache-ham-replace=POLICY` | eq | Hamming-hit: eq / strict / always |
| `--shared-cache-popularity=PCT` | 50 | anti-clustering penalty: effective weight = base / (1 + α × pick_count), α = PCT/100 |

And the related yals defaults that were tuned alongside:

| option | default | notes |
|---|---|---|
| `cutoff` | 20000 | flips per try; controls cache-cycle frequency |
| `maxtries` | INT_MAX | unbounded outer loop (run until SAT or terminate) |

(In the original code: `cutoff=10⁹`, `maxtries=1`. Both were misleading for
a long-running parallel solver — the 10⁹ default exhausted itself in ~30
min/worker, and `maxtries=1` meant no restarts ever happened by default.)

## Methodology

* **Solver**: palsat at HEAD of this branch, `-t 8` per process.
* **Hardware**: macOS Apple Silicon (M2, 8 cores) for early sweeps; later
  sweeps on AWS 192-physical-core Linux boxes via three machines.
* **Benchmarking**: `bench-parallel.sh` runs an (config × instance × seed)
  matrix with concurrent palsat processes capped by physical-core count.
  Outputs per-run logs, CSV, summary, per-instance breakdown, and a
  copy-paste-friendly `email.md` table.
* **Metric**: PAR-2 (penalized average runtime) = mean wall-clock per run,
  with timeouts charged at 2 × TIMEOUT seconds. Lower is better.
* **Secondary metric**: count of (seeds, instances) the config solved
  within the timeout.
* **Instances**: ntil-N.knf for N=30..50 (no-three-in-line problem encodings
  generated by `ntil-encode.c`). Difficulty grows roughly quadratically in N
  (variable count = N²).
* **Per-run timeout**: 60-900 s depending on instance hardness.
* **Seeds**: started at n=5, bumped to n=10 mid-tuning, final A/B/C at n=100.

## Timeline of sweeps and what each found

Each sweep tested a different set of one-knob and compound variants around
the then-current default. After most sweeps we promoted what looked like the
winning configuration to the default and ran the next sweep around the new
center.

### Baseline (sweep2): 60s budget, default vs no_cache

* 11 instances (ntil-30..40) × 5 seeds × 60s.
* `default` (original: cap=1024, ham=1%, warmup=0, pick=linear, no popularity, cutoff=2000): 52/55 SAT, PAR-2 13.38.
* `no_cache`: 47/55 SAT, PAR-2 22.03.
* **Apparent finding**: cache reduces PAR-2 by ~40% and wins 5 more
  instances.
* **In hindsight**: this was misleading. `no_cache` was running with
  cutoff=2000 — workers restarted every 5–10 ms and never developed any
  real per-worker search. The cache's pseudo-restarts looked beneficial
  against an artificially crippled baseline.

### Sweep1: 18 configs × 6 hard instances × 3 seeds

* First parameter sweep. Killed mid-run; partial data covered only ntil-35
  and ntil-36 (mid-difficulty, all configs solved easily).
* `combo_loose` (`cap=256 hamming=5% warmup=5`) had best PAR-2.
* **Action**: promoted combo_loose to new defaults.

### Sweep2: re-baseline at new defaults

* Confirmed the new defaults were a slight improvement.

### Sweep3: warmup variants

* Tested warmup ∈ {0, 5, 10, 20} and a popularity-penalty implementation
  added between sweeps.
* `warmup=0` consistently outperformed warmup=5; reverted to warmup=0.

### Sweep4: 15 configs × 3 hard instances × 4 seeds

* Tested `pick=uniform` vs `linear`, popularity variants.
* On the harder instances (ntil-41, ntil-43), `uniform_pop25` and
  `uniform_expl25` consistently topped the chart.
* **Action**: promoted `pick=uniform` and `explore=25` to defaults.

### Sweep5: validation at the new uniform+explore default

* The new default ranked **bottom-half** on 3 of 4 hard instances.
* `uniform_no_explore` was top-5 on every instance (avg rank 3.0).
* **Action**: reverted `explore=25 → 0`. Also bumped `cutoff=2000 → 10000`
  because `default_co10000` was consistently top-7.

### Sweep6: 15 configs around the post-sweep5 default

* Introduced compound experiments stacking popularity with cutoff.
* `default_pop25_co50000` (popularity=25 + cutoff=50000) was the runaway
  winner — top-3 on all 4 instances, avg rank 2.5. Beat `no_cache` on 3 of
  4 instances by 1.5-1.8× PAR-2.
* **Action**: promoted `popularity=25`, `cutoff=50000`.

### Sweep7: refine around sweep6 winner

* 15 configs varying popularity {10, 25, 50, 100}, cutoff {10000..50000},
  linear-pick variants.
* `default_pop50` showed up as top-3 on multiple instances; `default_pop10`
  was wildly variable.
* **Action**: bumped `popularity=25 → 50`. Also dropped `cutoff=50000 → 30000`
  based on observed sweet spot at 25000-30000.

### Sweep8: hard-instance tuning (ntil-45, 46)

* Tested with **n=10** seeds for first time. Bigger timeout (600s).
* `default_co20000` was the clear winner: avg rank 2.0, never below 3.
* `default_ham10` was the most consistent runner-up: rank 5 on both.
* **Action**: dropped `cutoff=30000 → 20000`, bumped `hamming=5 → 10`.

### Sweep9: validate the post-sweep8 default

* The new default (which combines sweep8's two top single-knob wins) ranked
  **13th out of 15** on ntil-46 and 8th on ntil-45.
* `default_co10000` was now the most robust (avg rank 3.0); `default_ham5`
  (just reverting the hamming bump) was avg rank 6.0.
* Critical observation: the same configuration ran with PAR-2 169 in
  sweep8 and PAR-2 314 in sweep9 on the same instance with the same seeds.
  System-level noise is ~2× the inter-config spread at the top.
* **No action**: defaults left unchanged; the data was inside the noise
  envelope.

### A/B/C final experiment: 3 configs × 3 instances × 100 seeds × 900s

The decisive validation:

| instance | no_cache | default | linear_pick |
|---|---|---|---|
| ntil-46 | **96/100** SAT, PAR-2 325 | 94/100, PAR-2 390 | 88/100, PAR-2 472 |
| ntil-43 | 80/100, PAR-2 608 | **83/100**, PAR-2 596 | 78/100, PAR-2 631 |
| ntil-45 | 60/100, PAR-2 959 | **62/100**, PAR-2 923 | 53/100, PAR-2 1084 |
| **total** | 236/300, mean PAR-2 631 | **239/300**, mean PAR-2 636 | 219/300, mean PAR-2 729 |

* `default` and `no_cache` are **statistically indistinguishable** in
  aggregate. 239 vs 236 SAT across 300 runs is a 1% difference. PAR-2
  differs by ~1%.
* `linear_pick` is robustly worse than both (−7% SAT count, +15% PAR-2).
* Per-instance ranking flips: no_cache wins ntil-46, default wins
  ntil-43 and ntil-45 — all by ≤6% margins.

## What we learned

### Robust findings (high confidence)

1. **`pick=uniform` is consistently better than `pick=linear`** in the
   cache configs, on hard instances. The cost-greedy bias of linear pick
   causes "groupthink" — workers converge on the same handful of best
   slots, losing diversification.
2. **`cutoff=2000` is too low.** At ~5-10 ms per try, the per-worker
   search never develops; cache cycling overhead dominates. Sensible
   range is 10000-50000.
3. **The shared cache feature breaks even with `no_cache`** at sensible
   cutoffs. The original 40% improvement was a baseline artifact.
4. **Very low cutoffs (200-500) catastrophically hurt cache configs**:
   excessive thrashing.

### Probable findings (medium confidence)

1. The cache provides **marginal benefit on harder instances** (ntil-43,
   ntil-45 saw `default` beating `no_cache` by 1-4% PAR-2) and
   **marginal harm on easier instances** (ntil-46 saw `no_cache` 17%
   ahead). Net wash.
2. **Hamming threshold in 5-10%** is the right zone. Below 1% kills
   dedup (everything looks unique); above 20% conflates distinct basins.
3. **Capacity beyond ~256 doesn't help.** Auto-sizing as 32 × threads is
   a reasonable rule of thumb.

### Uncertain (noisy)

1. **Popularity penalty level** (0, 25, 50, 75, 100) is highly variable.
   Sweep6 said pop=25 won; sweep7 said pop=50; sweep8 said still 50;
   sweep9 said no_pop. The current default (pop=50) is one defensible
   choice; pop=0 (off) is equally defensible.
2. **Warmup, explore, ham-replace policies** all showed instance-specific
   variability with no consistent winner.
3. **Per-instance "best" config drifts** — `uniform_pop25` won sweep4
   ntil-41 but cratered on sweep4 ntil-43; `default_pop10` won sweep7
   ntil-41 but was mid-pack on ntil-43.

### Counter-intuitive

1. **Stacking single-knob wins backfired.** When sweep8 showed
   `default_co20000` (#1) and `default_ham10` (#2) as the two best
   one-knob deltas, we combined them. Sweep9 ranked the combination
   **13th of 15**. Single-knob optima don't compose; knobs interact in
   ways we couldn't predict from one-axis-at-a-time tuning.
2. **More seeds reduced apparent effects, not increased them.** Larger
   N didn't sharpen the leaderboard — it confirmed that most of the
   ranking we saw at n=5 was noise.

## Methodology critique

1. **N=5 was too small for the differences we were trying to detect.**
   Same configuration on the same instance with the same seeds varied by
   2× across sweeps. Most "tuning wins" of <2× were artifacts.
2. **PAR-2 is dominated by timeouts on near-threshold instances.** At
   600s timeout on ntil-41, one extra timeout shifts PAR-2 by ~120 — and
   the top configs differed by less than that. We needed paired tests on
   per-seed outcomes, not unpaired averages.
3. **Sequential tuning rounds compounded noise into "drift."** Each
   round promoted what looked like a winner; over 9 sweeps we drifted
   away from a configuration (sweep6 winner) that might have been
   genuinely better than the final default — but we can't tell because
   we never re-tested it at n=100.
4. **Single-instance signals were over-trusted.** Each sweep tested on
   3-4 instances; what looked like a "consistent winner" was often
   actually variable, but we didn't have the data points to see it.
5. **System-level noise is real.** The 192-core box runs 24 parallel
   palsat × 8 threads = 192 threads on 192 physical cores. Memory
   bandwidth, thermal throttling, scheduling jitter — all show up at
   ~10-100% level in individual run times.
6. **Launch-order bias** in the bench harness: with 24-parallel and 150
   jobs per sweep, fast-finishing configs concentrate their late-seed
   runs in the thin-competition tail of the sweep and get artificially
   faster wall times. The current bench doesn't randomize launch order.

## Recommendations

### For palsat as a feature

* **Keep the cache feature implemented and available.** The code is clean
  and well-tested. The knobs work. It might help in regimes we haven't
  characterized (much harder instances, different problem classes).
* **Reconsider whether to enable the cache by default.** At current
  defaults, `--no-shared-cache` is statistically as good as enabled. Two
  defensible positions:
  - **Keep enabled by default** for slight expected upside on harder
    cases, accepting a slight expected downside on easier ones.
  - **Default to disabled**, leave it as an opt-in for users who have
    instance-specific evidence it helps them. Cleaner default behavior.
* **Strongly document `pick=uniform` as the recommended pick scheme**
  whenever the cache is enabled. This was the only consistently robust
  tuning finding.

### For yals defaults (independent of cache)

* **`cutoff=2000` was the wrong default.** A reasonable range is
  10000-30000. The exact value is less important than not being too low.
* **`maxtries=1` was the wrong default.** Any long-running solver should
  have `maxtries` set very high (we use INT_MAX). Otherwise the solver
  silently exits after one try.

### For future tuning of any palsat feature

* **Use n ≥ 50 seeds per config** when measuring fine differences.
* **Use paired statistical tests** (Wilcoxon signed-rank) on per-seed
  outcomes, not unpaired averages.
* **Test against `no_cache` at n=100 first** to establish whether the
  feature provides any benefit at all, before tuning details.
* **Cross-validate**: tune on instance set A, validate on instance set
  B. Don't promote a default based on the sweep that selected it.
* **Don't compose single-knob optima blindly.** When two changes both
  look like wins, test the compound directly before promoting.

## Open questions / future work

* **Does the cache help on very-hard instances** where no_cache fails to
  solve at all? The currently-running overnight stress test on ntil-47,
  48, 50 at 3600s × n=100 should answer this. If `default` and
  `sweep6_winner` solve materially more of these than `no_cache`, the
  feature has a real use case at the hardness frontier.
* **Does the cache help on different problem classes?** We only tested
  ntil. Magic-square (combinatorial design), MaxSAT problems, or
  industrial CNFs might have different structure where cooperation
  matters more.
* **Did we under-tune fundamentally diversification-related knobs?**
  `warmup`, `explore`, `popularity` each showed instance variability we
  couldn't pin down. Maybe there's an instance-adaptive scheme (e.g.,
  start with no cache and turn it on after a stagnation signal) that
  would actually win.
* **Anti-clustering bias** (popularity) showed the most "almost-real"
  signal but never robustly. Worth revisiting with a more careful
  experimental design.
* **Different cooperation mechanisms**: clause learning sharing,
  best-assignment broadcast, MAB-based strategy selection. The shared
  cache is one of many possible cooperation schemes; the null result
  here doesn't generalize to all of them.

## Raw data and infrastructure

All sweep data is preserved in working directories at `/tmp/bench-baseline`,
`/tmp/bench-sweep{1..9}`, etc. (not committed; sizes range from KB to MB).
Configs files are in `bench/configs-*.tsv`.

Benchmark infrastructure (committed in repo):

* `bench-parallel.sh` — main parallel runner, trap-based aggregation.
* `bench-aggregate.sh` — rebuild summary from `rows/` if a run gets
  killed before aggregation.
* `sweep-one.sh` — single-command wrapper around bench-parallel that
  produces an email-ready table.
* `bench/configs-*.tsv` — config sets used in each sweep.
* `bench/instances-*.txt` — instance lists.
* `bench-results/README.md` — output-directory conventions.

Solver-side implementation:

* `solver/yals.c`: `YalsSharedCache` struct, cache operations, and
  `yals_shared_cache_cycle()` hook in `yals_restart_inner`.
* `solver/yals.h`: public API (config struct, `yals_shared_cache_new`,
  `yals_set_shared_cache`).
* `solver/main.c`: palsat driver wires the cache up after parsing and
  exposes the CLI flags.
* `solver/options.h`: `cutoff` and `maxtries` defaults.

## Closing assessment

The shared assignment cache is a defensible, cleanly-implemented feature
that does what it says on the tin — but on the workload we tested, it
doesn't provide a measurable average benefit over running the same
workers independently. That's a real negative result, useful for ruling
out a particular hypothesis about parallel SAT solving. The tuning
process surfaced one robust finding (`pick=uniform`), a few likely-true
heuristics (cutoff range, hamming range), and a clear lesson about the
limits of single-knob sequential tuning under noise.

If you want the cache feature to be useful in practice, the next steps
would be: (a) characterize the instance regime where it does help (the
currently-running overnight experiment may answer this), (b) consider
fundamentally different cooperation schemes, or (c) leave it as an opt-in
and document the conditions under which we expect it to help.
