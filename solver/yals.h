/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and manager  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef LIBYALS_H_INCLUDED
#define LIBYALS_H_INCLUDED

/*------------------------------------------------------------------------*/

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/time.h>
#include "stack.h"
#include "options.h"
#include "assert.h"
#include "heap.h"

#if defined(__linux__)
#include <fpu_control.h> // Set FPU to double precision on Linux.
#endif


/*------------------------------------------------------------------------*/

#define STRATSTEMPLATE \
  STRAT (cached,1); \
  STRAT (pol,1);

#define STRAT(NAME,ENABLED) int NAME

/*------------------------------------------------------------------------*/

typedef void * (*YalsMalloc)(void*,size_t);
typedef void * (*YalsRealloc)(void*,void*,size_t,size_t);
typedef void (*YalsFree)(void*,void*,size_t);

#define TYPECLAUSE 0
#define TYPECARDINALITY 1


#define YALS_INT64_MAX (0x7fffffffffffffffll)
#define YALS_DEFAULT_PREFIX "c "
#define YALS_DOUBLE_MAX 1.79769e+308

/*

  Data Structures

*/

// (score,lit) used for selecting top-k scores from heap
typedef struct {
  double score;
  int lit;
} Lit_Score;

typedef unsigned Word;

typedef struct YalsSharedCache YalsSharedCache;
typedef struct YalsProbePool YalsProbePool;

#ifndef NYALSMEMS
#define ADD(NAME,NUM) \
do { \
  yals->stats.mems.all += (NUM); \
  yals->stats.mems.NAME += (NUM); \
} while (0)
#else
#define ADD(NAME,NUM) do { } while (0)
#endif

#define INC(NAME) ADD (NAME, 1)

typedef struct RNG { unsigned z, w; } RNG;

typedef struct Mem {
  void * mgr;
  YalsMalloc malloc;
  YalsRealloc realloc;
  YalsFree free;
} Mem;

typedef struct Strat { STRATSTEMPLATE } Strat;

// stats used throughout execution and displayed on exit
typedef struct Stats {
  int  card_maxstacksize;
  int best, worst, last, tmp, maxstacksize;

  // cardinality additions
  int best_cardinality, best_clauses;
  // end cardinality additions

  int64_t nheap_updated;

  // max sat weights
  double maxs_tmp_weight, maxs_best_cost, maxs_worst_cost, maxs_last;
  int maxs_best_hard_cnt;
  double maxs_card_best_weight,maxs_clause_best_weight;
  int maxs_card_best_hard_cnt,maxs_clause_best_hard_cnt;

  int maxs_best_soft_cnt;
  int maxs_card_best_soft_cnt,maxs_clause_best_soft_cnt;
  struct { volatile double initialization, weight_transfer, make_time, break_time, var_selection, soft_var_selection, hard_var_selection; } maxs_time;
  // end max sat weights

  int64_t flips, bzflips, hits, unsum, get_random_sat_cnt, get_random_sat_missed;
  // Value of `flips` at the start of the current probe (the last time this
  // worker began from a freshly picked assignment). Used to report how many
  // flips a probe needed to reach the global best score.
  int64_t probe_start_flips;
  // 1 iff the current probe started from a freshly generated random
  // assignment (not a cached/best/keep/all-polarity pick, and not overridden
  // by the shared cache). Only random-started probes contribute to the
  // global-best tracker.
  int probe_random;
  struct {
    struct { int64_t count; } outer;
    struct { int64_t count; } inner;
    int64_t bypassed;  // # times --bypass extended a probe past cutoff
  } restart;
  struct { struct { int chunks, lnks; } max; int64_t unfair; } queue;
  struct { int64_t inserted, replaced, skipped; } cache;
  struct { int64_t search, neg, falsepos, truepos; } sig;
  struct { int64_t def, rnd; } strat;
  struct { int64_t best, cached, keep, pos, neg, rnd; } pick;
  struct { int64_t count, moved; } defrag;
  struct { size_t current, max; } allocated;
  struct { volatile double total, defrag, restart, entered; } time;
#ifdef __GNUC__
  volatile int flushing_time;
#endif
#ifndef NYALSMEMS
  struct { long long all, crit, lits, occs, read, update, weight; } mems;
#endif
#ifndef NYALSTATS
  int64_t * inc, * dec, broken, made; int nincdec;
  struct { unsigned min, max; } wb;
#endif
} Stats;

typedef struct Limits {
#ifndef NYALSMEMS
  int64_t mems;
#endif
  int64_t flips;
  struct { int min; } report;
  int term;
} Limits;

typedef struct Lnk {
  int cidx;
  struct Lnk * prev, * next;
} Lnk;

typedef union Chunk {
  struct { int size; union Chunk * next; };
  Lnk lnks[1]; // actually of 'size'
} Chunk;

typedef struct Queue {
  int count, chunksize, nchunks, nlnks, nfree;
  Lnk * first, * last, * free;
  Chunk * chunks;
} Queue;

typedef struct Exp {
  struct { STACK(double) two, cb; } table;
  struct { unsigned two, cb; } max;
  struct { double two, cb; } eps;
} Exp;

typedef struct Opt { int val, def, min, max; } Opt;

typedef struct Opts { char * prefix; OPTSTEMPLATE } Opts;

typedef struct Callbacks {
  double (*time)(void);
  struct { void * state; int (*fun)(void*); } term;
  struct { void * state; void (*lock)(void*); void (*unlock)(void*); } msg;
} Callbacks;

typedef unsigned char U1;
typedef unsigned short U2;
typedef unsigned int U4;

typedef struct FPU {
#ifdef __linux__
  fpu_control_t control;
#endif
  int saved;
} FPU;

typedef struct {  
    STACK (int) clauses;
  } LitClauses;

 typedef struct {  
     STACK (int) neighbors;
  } ClauseNeighboursDups, ClauseNeighbours;

  typedef struct {  
     STACK (int) neighbors;
  } ClauseNeighboursDupRemoved;

typedef STACK (int) STACK_INT;


// structure for weight-transfer algorithm
typedef struct DDFW {

  LitClauses* lit_clauses_map;
 
  /** Whole neighborhood for all the clauses **/

  int neighbourhood_at_init;
  /** On demand neighborhood for a clause **/

  int prev_unsat_weights;
 
 
  double * ddfw_clause_weights; // ddfw weight of each clause
  double * unsat_weights; // ddfw weight gain for flipping lit (unsat to sat)
  double * sat1_weights; // ddfw weight lost for flipping lit (sat to unsat)
  int init_weight_done;
  STACK (int) satisfied_clauses;
 

  int last_flipped;


  int sideways;

  // max_weighted_neighbour: initial weights are equal for all the clauses. just initialize the first neighbor of a clause as the max_weight neighbor
  // max_weighted_neighbour: needs to be updated after each weight transfers between a clause and its max neighbors
  int * max_weighted_neighbour;

  int * clauses_unsat;
  int * clasues_sat_one_lit;

  // old stack implementation (now use heap)
  int break_weight, break_weight_temp;
  int * uwrvs;
  int uwrvs_size;
  double * uwvars_gains;
  int * non_increasing;
  int non_increasing_size;
  int * helper_hash_clauses;
  int * helper_hash_vars;

  STACK (int) helper_hash_changed_idx;
  STACK (int) helper_hash_changed_idx1;
  int best_var;
  double best_weight;
  int * sat_count_in_clause; // number of satisfied lits within a clause
  STACK (int) sat_clauses;
  int local_minima, wt_count;
  int conscutive_lm, count_conscutive_lm, consecutive_lm_length, max_consecutive_lm_length;


  STACK_INT uvars; // hard variables in falsified cosntraints
  int * uvar_pos;
  STACK_INT uvars_changed; // vars with changed weight-gain (need to be updated in the heap)
                          // both soft and hard variables
  int * uvar_changed_pos; // pos in stack
  int * var_unsat_count; // number of falsified constraints a variable occurs in

  double weight_update_time, uwrv_time, flip_time, wtransfer_time, neighborhood_comp_time;
  double update_candidate_sat_clause_time, compute_uwvars_from_unsat_clauses_time; 
  double init_neighborhood_time;

  int ddfw_active;
  int recent_max_reduction;
  int flip_span;
  int prob_check_window;
  int alg_switch;

  double time_ddfw;
  int flips_ddfw_temp, flips_ddfw;

  double sum_uwr;
  double clsselectp;
  double ddfwstartth;
  int guaranteed_uwrvs, missed_guaranteed_uwvars;
  unsigned source_not_selected;
  unsigned total_transfers;

  heap uvars_heap; // heap for hard variables (all variables if not MaxSAT)
  heap uvars_heap_soft; // heap for soft variables

  // maxsat
  STACK_INT uvars_soft; // soft variables in falsified cosntraints
  int * uvar_pos_soft; 
  int * var_unsat_count_soft; // number of falsified constraints a soft variable occurs in

  double * unsat_weights_soft, * sat1_weights_soft;

  int reset_weights_on_restart;

  /*
    additional data for cardinality constraint handling
  */

  STACK (int) card_helper_hash_changed_idx;
  int * card_helper_hash_clauses;
  int * card_sat_count_in_clause;
  int * card_sat_dirty; // 1 iff the sat/unsat partition may have drifted while over-satisfied (needs a full re-sort on re-entry to critical)
  double * ddfw_card_weights; // cardinality constraint ddfw weights

  // Preallocated per-thread scratch for the weight-transfer source-selection
  // path (each Yals is per-thread, so these need no locking). Avoids the
  // malloc/free that used to happen at every local minimum -- the allocator
  // locks were a contention source under high thread counts.
  int    * xfer_sources;   // [xfer_slots] source ids   (transfer_weights_for_*)
  int    * xfer_types;     // [xfer_slots] source types
  int      xfer_slots;
  int    * rtk_src;        // [rtk_target] strict pool  (get_random_sat_top_k)
  int    * rtk_tps;        // [rtk_target]
  double * rtk_wts;        // [rtk_target]
  int    * rtk_fsrc;       // [rtk_k] relaxed-fallback pool
  int    * rtk_ftps;       // [rtk_k]
  double * rtk_fwts;       // [rtk_k]
  int      rtk_target;     // randtour*randk
  int      rtk_k;          // randk
  int    * tkm_srcs;       // grows lazily, persists across calls
  int    * tkm_tps;        //   (get_top_k_max_weight_sat_clause)
  double * tkm_wts;
  int      tkm_cap;

  double * card_clause_calculated_weights; // cache of calculted weightes (not in use)

  // --litheap: per-literal max-weight neighbor heaps (mixed clause/card).
  // See the "--litheap" block in yals.c for the encoding.
  int nbr_built;
  int nbr_E, nbr_nlits, nbr_ncons;
  int * nbr_con;     // [E] edge -> unified constraint id (clause u<nclauses; else card)
  int * nbr_lit;     // [E] edge -> literal position (get_pos)
  int * nbr_heap;    // [E] edge enumeration by literal (slots [lstart[p], lstart[p+1]) hold edges with literal p, in arrival order)
  int * nbr_cstart;  // [ncons+1] constraint -> first edge (constraint-major)
  int * nbr_lstart;  // [nlits+1] literal position -> first slot in nbr_heap

  // --topk: per-literal top-K list of heaviest neighbors (shares cstart,
  // lstart, con, lit with the nbr_* graph but uses its own list/pos arrays).
  int topk_built;
  int topk_k;        // K (entries per literal)
  int * topk_list;   // [nlits * K] flat array; slots p*K .. p*K + count[p] hold the entries (edge ids), sorted by (weight, id) descending
  int * topk_count;  // [nlits] current size per literal (0..K)
  int * topk_pos;    // [E] edge -> index within owning literal's slice (0..K-1), -1 if not in list
  double * nbr_w;    // [E] edge -> cached weight of nbr_con[e]; kept in sync on every weight change so yals_nbr_better avoids the nbr_con indirection + clause/card branch per comparison
  // Diagnostics (printed by yals_print_stats when --topk>0).
  int64_t topk_stat_q;             // total yals_topk_best queries
  int64_t topk_stat_rebuild;       // queries that triggered an empty-list rebuild
  int64_t topk_stat_eligible;      // queries that returned an eligible source
  int64_t topk_stat_no_eligible;   // queries that returned -1 (caller falls through to scan)
  int64_t topk_stat_walked;        // sum of positions visited across all queries (sum of 1..count for each query)
  int64_t topk_stat_diverged;      // (TOPK_VERIFY=1 env var) queries where top-K pick != full-scan pick
  int topk_verify;                 // set from TOPK_VERIFY env at build time

  // Per-variable last-flip step number (stats.flips value at the moment v
  // was last flipped). Used by:
  //   - --tabu: v is tabu while stats.flips - last_flipped[v] < opts.tabu.val
  //   - avg-age stat in "new minimum" prints
  // Always allocated when DDFW is built. Indexed by variable id (1..nvars).
  // 0 is the "never flipped yet" sentinel -- callers gate on `prev > 0`
  // so these vars don't pollute the age stat or appear tabu at startup.
  int64_t * tabu_last_flipped;
  // Sliding-window average of "age" of the just-flipped variable, where
  // age = stats.flips - prev_flip_step. Implemented as a ring buffer of
  // size opts.age_window.val. Vars that have never been flipped before
  // (last_flipped[v] == 0) contribute no sample. The window is NOT
  // reset at "new minimum" prints -- avg_age is the continuous rolling
  // average over the last K samples.
  int64_t * age_window_buf;   // ring of K int64_t
  int      age_window_size;   // K
  int      age_window_head;   // next-write index in [0, K)
  int      age_window_count;  // 0..K (grows until full, then stays at K)
  int64_t  age_window_sum;    // sum of buf[0..count-1]

  // Sliding-window Hamming distance: HD between the current assignment and
  // the assignment K flips ago. Equivalently, # of vars flipped an odd
  // number of times within the last K flips. Same K = age_window_size.
  // Per-flip update is O(1): toggle parity of the new flipping var, and
  // if the ring is full, evict the oldest var id and toggle its parity
  // too. hd_window tracks the running count of vars with odd parity.
  // hd_sum / hd_samples accumulates per-flip HD to produce avg_hd over
  // the same window as avg_age (one sample per flip, but only once the
  // ring has filled, so HD is meaningful w.r.t. exactly K-ago).
  int    * hd_ring;           // ring of K var ids
  unsigned char * hd_parity;  // per-var parity (0/1) within window; size nvars+1
  int      hd_ring_head;      // next-write index in [0, K)
  int      hd_ring_count;     // 0..K (grows until full, then stays at K)
  int      hd_window;         // running HD = # vars with odd parity in window
  // Rolling K-window mean of hd_window (one sample per flip).
  int    * hd_value_ring;     // ring of K int samples of hd_window
  int      hd_value_head;
  int      hd_value_count;
  int64_t  hd_value_sum;
  // Last stats.flips value at which an --hd_restart trigger fired (used to
  // enforce a minimum K-flip spacing between consecutive HD-triggered
  // restarts, mirroring the cutoff's natural spacing).
  int64_t  hd_last_restart_flip;

  // Per-probe best-score log. A "probe" is the work between consecutive
  // inner restarts: from yals_pick_assignment to the next cutoff (or
  // --hd_restart trigger). Each entry is stats.tmp at the *end* of a
  // probe (i.e. the best nunsat reached during that probe). Skips the
  // initial pre-flip pseudo-restart and any probe with no flips (tmp
  // still INT_MAX). Printed as a histogram by yals_stats at end of run.
  STACK (int) probe_bests;

  // --oldestsource: LRU doubly-linked list over all constraints (unified id =
  // clause cidx for u<nclauses; card cidx + nclauses else). Head = least
  // recently used as a source. Allocated only when --oldestsource is on.
  int * oldsrc_prev;
  int * oldsrc_next;
  int oldsrc_head, oldsrc_tail, oldsrc_ncons;

} DDFW;

// structure for stack constaining falsified constraints,
// also stores the weight of falsified constraints in the stack
typedef struct UNSAT_STACK {
  int usequeue; int hard_cnt; double maxs_weight; Queue queue; STACK_INT stack;
} UNSAT_STACK;

// structure for solver
typedef struct Yals {
  RNG rng;
  FILE * out;
  UNSAT_STACK unsat; // falsified hard (all if not MaxSAT) constraints
  int nvars, * refs; int64_t * flips;
  STACK(signed char) mark;
  int trivial, mt, pick;
  Word * vals, * best, * tmp, * clear, * set, *curr; int nvarwords;
  STACK(int) cdb, trail, phases, clause, mins;
  int satcntbytes; union { U1 * satcnt1; U2 * satcnt2; U4 * satcnt4; };
  int * occs, noccs;
  int * pos, * lits; Lnk ** lnk;
  int * crit;
  int nclauses, nbin, ntrn, minlen, maxlen; double avglen;
  STACK(unsigned) breaks; STACK(double) scores; STACK(int) cands;
  STACK(Word*) cache; int cachesizetarget; STACK(Word) sigs;
  STACK(int) minlits;
  Callbacks cbs;
  Limits limits;
  Strat strat;
  Stats stats;
  Opts opts;
  Mem mem;
  FPU fpu;
  Exp exp;
  DDFW ddfw;
  STACK (int) clause_size;
  int wid;
  int consecutive_non_improvement, last_flip_unsat_count;

  /*
    additional data for max sat
  */
  UNSAT_STACK unsat_soft; // falsified soft constraints

  int using_maxs_weights, is_pure, hard_polarity; // 0/1 indicating type of problem
  int cardinality_is_hard; // all hard constraints are cardinality constraints (for more efficient random sat selection)
  STACK (double) maxs_clause_weights; // soft constraint costs
  double parsed_weight;
  double maxs_hard_weight; // weight of hard constraints
  double maxs_acc_hard_weight;
  int * hard_clause_ids; // clauses that are hard (=1) or soft (=0)
  unsigned char * clause_has_neg;  // --heavy: 1 if clause cidx contains any negative literal

  int * pos_soft;
  int * card_pos_soft; 

  STACK (Lit_Score) lit_scores;

  int weight_transfer_soft; // allow transferring to soft consrtaints
  int current_weight_transfer_soft;

  int maxs_hard_offset; // offset for hard ddfw weight in MaxSAT inner loop

  double propagated_soft_weight; // if soft constraints are falsified in unit propagation, store their costs

  /*
    additional data for cardinality constraint handling
  */
  UNSAT_STACK card_unsat; // falsified hard (all) constraints
  UNSAT_STACK card_unsat_soft; // falsified soft constraints

  int card_crit;

  STACK(int) card_cdb; // bound, literals, 0, ...
  STACK (int) card_size;
  int * card_lits, * card_refs;
  int * card_occs, card_noccs;

  int bound, card_nclauses;

  double card_avglen;

  int * card_pos; // Lnk ** card_lnk; // Only stack currently

  int card_minlen, card_maxlen;
  int card_satcntbytes; union { U1 * card_satcnt1; U2 * card_satcnt2; U4 * card_satcnt4; };
  // int ** card_crit; // critical literals for a cardinality constraint

  STACK (double) maxs_card_weights; // soft constraint costs
  int * hard_card_ids; // cardinality constraints that are hard (=1) or soft (=0)
  unsigned char * card_has_neg;  // --heavy: 1 if card cidx contains any negative literal

  // Optional pointer to a process-wide cache of assignments shared across
  // palsat workers. NULL when no shared cache is attached.
  YalsSharedCache * shared_cache;
  YalsProbePool * probe_pool;

} Yals;

/*------------------------------------------------------------------------*/

Yals * yals_new ();
void yals_del (Yals *);

/*------------------------------------------------------------------------*/



Yals * yals_new_with_mem_mgr (void*, YalsMalloc, YalsRealloc, YalsFree);

/*------------------------------------------------------------------------*/

int yals_setopt (Yals *, const char * name, int val);
void yals_setprefix (Yals *, const char *);
void yals_setout (Yals *, FILE *);
void yals_setphase (Yals *, int lit);
void yals_setflipslimit (Yals *, long long);
void yals_setmemslimit (Yals *, long long);

int yals_getopt (Yals *, const char * name);
void yals_usage (Yals *);
void yals_showopts (Yals *);

/*------------------------------------------------------------------------*/

void yals_add (Yals *, int lit);

int yals_sat (Yals *);

/*------------------------------------------------------------------------*/

long long yals_flips (Yals *);
long long yals_mems (Yals *);

int yals_minimum (Yals *);
int yals_lkhd (Yals *);
int yals_deref (Yals *, int lit);

const int * yals_minlits (Yals *);


int yals_flip_count (Yals *yals);

int yals_nunsat_external (Yals *yals);

/*------------------------------------------------------------------------*/

void yals_stats (Yals *);

// Shared probe-best pool: a histogram of per-probe stats.tmp values
// pooled across all workers, used by --bypass to gauge how the
// current probe's best compares to the global distribution. Lock-
// protected; reads/writes are infrequent (~1 per probe per worker)
// so a single mutex is fine.
YalsProbePool * yals_probe_pool_new (void);
void yals_probe_pool_delete (YalsProbePool *);
void yals_set_probe_pool (Yals *, YalsProbePool *);
// Print a single global line summarizing --bypass usage across `n`
// workers (count + fraction of total cutoff hits that were bypassed).
// Mirror of yals_print_combined_probe_hist for the bypass counter.
void yals_print_combined_bypass_stats (Yals ** ys, int n);

// Print the --heat per-variable counter (one line per nonzero variable,
// sorted by count descending). Pool is read once; safe to call after
// all workers have stopped. No-op if --heat is disabled on every worker.
void yals_print_combined_heat (Yals ** ys, int n);

// After SAT is found, print the constraints (clauses + cards) whose
// "heat slack" is lowest -- the constraints that the heat map would be
// closest to falsifying. For each constraint, slack = (sum of literal
// scores) - bound, where positive literal x scores heat[x]/probes,
// negative literal -x scores 1 - heat[x]/probes, and a plain clause is
// treated as a card with bound 1. Lowest `top_n` printed (or all if
// fewer). Reads the shared probe_pool's heat[]; uses `winner` only for
// clause / card iteration.
void yals_print_heat_slack (Yals * winner, int top_n);

// Print a single probe-best histogram aggregated across `n` workers.
// Each worker's per-probe scores (yals->ddfw.probe_bests) are merged
// into one flat list before bucketing. Use `n=1` for sequential runs.
// Output is emitted via yals_msg on ys[0] so it picks up that worker's
// prefix; safe to call with all workers (palsat) or just the single
// active solver (CaLFwSAT).
void yals_print_combined_probe_hist (Yals ** ys, int n);

/* Average weight per constraint length (clauses and cardinality
   constraints separately). For palsat, call on the winning thread. */
void yals_print_length_weights (Yals *);

/*------------------------------------------------------------------------*/

void yals_seterm (Yals *, int (*term)(void*), void*);

void yals_setime (Yals *, double (*time)(void));

void yals_setmsglock (Yals *,
       void (*lock)(void*), void (*unlock)(void*), void*);

/*------------------------------------------------------------------------*/

// Shared assignment cache (used by palsat to share starting assignments
// across worker threads). The cache holds up to `capacity` assignments;
// at each restart a worker inserts its best-of-try assignment and then
// picks a new starting assignment from the cache by weighted random
// selection (better cost -> higher weight). A slot picked by a worker is
// reserved until that worker reaches its next restart, so two workers
// never start from the same cached assignment concurrently.

// Defaults (set by yals_shared_cache_config_init):
//   capacity=256, hamming_percent=5, pick=linear, warmup=5, explore=0,
//   replace_full=worse-only, ham_replace=eq, insert=always.

// Pick-weight schemes for selecting from the cache.
#define YSC_PICK_LINEAR  0  // weight = max_cost - cost + 1     (default)
#define YSC_PICK_RANK    1  // weight = (N - rank)              (best=highest)
#define YSC_PICK_SOFTMAX 2  // weight = exp((max - cost) / T)   (temp=softmax_temp_x10/10)
#define YSC_PICK_UNIFORM 3  // weight = 1                       (no bias)
#define YSC_PICK_INV     4  // weight = 1 / (cost + 1)

// Replacement policy when no Hamming-near slot AND cache is full.
#define YSC_REPLACE_WORSE_ONLY  0  // replace worst unreserved slot with cost >= new (default)
#define YSC_REPLACE_ALWAYS      1  // always replace worst unreserved slot (even if cache better)
#define YSC_REPLACE_NEVER       2  // skip insertion

// Replacement policy when a Hamming-near slot IS found.
#define YSC_HAM_REPLACE_EQ      0  // replace if new cost <= existing (default)
#define YSC_HAM_REPLACE_STRICT  1  // replace only if strictly better
#define YSC_HAM_REPLACE_ALWAYS  2  // always replace

// Insert gating.
#define YSC_INSERT_ALWAYS    0  // insert at every restart (default)
#define YSC_INSERT_IMPROVED  1  // insert only if cost <  start-of-try cost

typedef struct YalsSharedCacheConfig {
  int capacity;            // max number of slots (e.g. 1024)
  int hamming_percent;     // near-dup threshold = percent * V / 100 bits
  int pick_weight;         // YSC_PICK_*
  int softmax_temp_x10;    // temperature * 10 (used only by softmax). 10 = T=1.0
  int replace_full;        // YSC_REPLACE_*  (cache-full, no-ham-match path)
  int ham_replace;         // YSC_HAM_REPLACE_*
  int warmup;              // per-worker: skip shared pick for first N restarts
  int explore_pct;         // 0-100: chance to ignore weights, pick uniformly
  int insert_mode;         // YSC_INSERT_*  (always / improved-over-start)
  int popularity_pct;      // 0-100: anti-clustering penalty for popular slots.
                           //   effective_weight = base / (1 + (pct/100) * pick_count)
                           //   0 = no penalty (default), 100 = strong penalty.
} YalsSharedCacheConfig;

// Initialize a config struct with the current defaults.
void yals_shared_cache_config_init (YalsSharedCacheConfig *);

YalsSharedCache * yals_shared_cache_new (int nworkers,
                                         const YalsSharedCacheConfig *);
void yals_shared_cache_delete (YalsSharedCache *);
void yals_set_shared_cache (Yals *, YalsSharedCache *);
void yals_shared_cache_stats (YalsSharedCache *);
void yals_shared_cache_config_dump (const YalsSharedCacheConfig *, FILE *);

/*------------------------------------------------------------------------*/



unsigned yals_satcnt (Yals * yals, int cidx);

void yals_add_vars_to_uvars (Yals* yals, int cidx, int constraint_type);
void yals_delete_vars_from_uvars (Yals* yals, int cidx, int constraint_type);

int yals_pick_from_list_scores (Yals * yals);
void yals_flip_value_of_lit (Yals * yals, int lit);
void yals_make_clauses_after_flipping_lit (Yals * yals, int lit);
void yals_break_clauses_after_flipping_lit (Yals * yals, int lit);
void yals_update_sat_and_unsat (Yals * yals);

int yals_pick_literal_from_heap (Yals * yals, int soft);

void yals_ddfw_update_score_function_weights (Yals * yals);

void yals_remove_trailing_bits (Yals * yals);
void yals_set_units (Yals * yals);

void yals_ddfw_update_changed_var_weights (Yals * yals);

/*
--------------------------------------------------------------------------------
inlined utilities
*/

#define LD_BITS_PER_WORD 5
#define BITS_PER_WORD (8*sizeof (Word))
#define BITMAPMASK (BITS_PER_WORD - 1)

#define WORD(BITS,N,IDX) \
  ((BITS)[ \
    assert ((IDX) >= 0), \
    assert (((IDX) >> LD_BITS_PER_WORD) < (N)), \
    ((IDX) >> LD_BITS_PER_WORD)])

#define BIT(IDX) \
  (((Word)1u) << ((IDX) & BITMAPMASK))

#define GETBIT(BITS,N,IDX) \
  (WORD(BITS,N,IDX) & BIT(IDX))

#define SETBIT(BITS,N,IDX) \
  do { WORD(BITS,N,IDX) |= BIT(IDX); } while (0)

#define CLRBIT(BITS,N,IDX) \
  do { WORD(BITS,N,IDX) &= ~BIT(IDX); } while (0)

#define NOTBIT(BITS,N,IDX) \
  do { WORD(BITS,N,IDX) ^= BIT(IDX); } while (0)

/*------------------------------------------------------------------------*/

#define MIN(A,B) (((A) < (B)) ? (A) : (B))
#define MAX(A,B) (((A) > (B)) ? (A) : (B))
#define ABS(A) (((A) < 0) ? (assert ((A) != INT_MIN), -(A)) : (A))

#define SWAP(T,A,B) \
  do { T TMP = (A); (A) = (B); (B) = (TMP); } while (0)

/*------------------------------------------------------------------------*/

#define LENSHIFT 6
#define MAXLEN ((1<<LENSHIFT)-1)
#define LENMASK MAXLEN


static inline int compare_lit_score (const void *a, const void *b) {
  Lit_Score *A = (Lit_Score *)a;
  Lit_Score *B = (Lit_Score *)b;
  if (A->score < B->score) return 1;
  else if (A->score > B->score) return -1;
  else return 0;
}


/*------------------------------------------------------------------------*/

#define assert_valid_occs(OCCS) \
  do { assert (0 <= OCCS), assert (OCCS < yals->noccs); } while (0)

#define assert_valid_idx(IDX) \
  do { assert (0 <= IDX), assert (IDX < yals->nvars); } while (0)

#define assert_valid_cidx(CIDX) \
  do { assert (0 <= CIDX), assert (CIDX < yals->nclauses); } while (0)

#define assert_valid_len(LEN) \
  do { assert (0 <= LEN), assert (LEN <= MAXLEN); } while (0)

#define assert_valid_pos(POS) \
  do { \
    assert (0 <= POS), assert (POS < COUNT (yals->unsat.stack)); \
} while (0)


#define assert_valid_card_occs(OCCS) \
  do { assert (0 <= OCCS), assert (OCCS < yals->card_noccs); } while (0)

#define assert_valid_card_cidx(CIDX) \
  do { assert (0 <= CIDX), assert (CIDX < yals->card_nclauses); } while (0)

#define assert_valid_card_len(LEN) \
  do { assert (0 <= LEN), assert (LEN <= MAXLEN); } while (0)


#define assert_valid_card_pos(POS) \
  do { \
    assert (0 <= POS), assert (POS < COUNT (yals->card_unsat.stack)); \
} while (0)


/*
--------------------------------------------------------------------------------
inlined data structure accesses 
*/

static inline int get_pos (int lit)
{
  return  2*(abs (lit)) + (lit < 0);
}

static inline int * yals_refs (Yals * yals, int lit) {
  int idx = ABS (lit);
  assert_valid_idx (idx);
  assert (yals->refs);
  return yals->refs + 2*idx + (lit < 0);
}

static inline int * yals_card_refs (Yals * yals, int lit) {
  int idx = ABS (lit);
  assert_valid_idx (idx);
  assert (yals->card_refs);
  return yals->card_refs + 2*idx + (lit < 0);
}

static inline int * yals_occs (Yals * yals, int lit) {
  int occs;
  INC (occs);
  occs = *yals_refs (yals, lit);
  assert_valid_occs (occs);
  return yals->occs + occs;
}

static inline int * yals_card_occs (Yals * yals, int lit) {
  int occs;
  INC (occs);
  occs = *yals_card_refs (yals, lit);
  assert_valid_card_occs (occs);
  return yals->card_occs + occs;
}

static inline int yals_val (Yals * yals, int lit) {
  int idx = ABS (lit), res = !GETBIT (yals->vals, yals->nvarwords, idx);
  if (lit > 0) res = !res;
  return res;
}

static inline int yals_polarity (Yals * yals, int lit) {
  int true_lit = yals_val (yals, lit) ? lit : -lit;
  return ABS(true_lit)/ true_lit;
}

/*
--------------------------------------------------------------------------------
inlined logging
*/

#ifndef NDEBUG
#define LOG(ARGS...) \
do { \
  if (!yals->opts.logging.val) break; \
  yals_log_start (yals, ##ARGS); \
  yals_log_end (yals); \
} while (0)
#define LOGLITS(LITS,ARGS...) \
do { \
  const int * P; \
  if (!yals->opts.logging.val) break; \
  yals_log_start (yals, ##ARGS); \
  fprintf (yals->out, " clause :"); \
  for (P = (LITS); *P; P++) \
    fprintf (yals->out, " %d", *P); \
  yals_log_end (yals); \
} while (0)
#define LOGCIDX(CIDX,ARGS...) \
do { \
  const int * P, * LITS = yals_lits (yals, (CIDX)); \
  if (!yals->opts.logging.val) break; \
  yals_log_start (yals, ##ARGS); \
  fprintf (yals->out, " clause %d :", (CIDX)); \
  for (P = (LITS); *P; P++) \
    fprintf (yals->out, " %d", *P); \
  yals_log_end (yals); \
} while (0)
#define LOGCARDCIDX(CIDX,ARGS...) \
do { \
  const int * P, * LITS = yals_card_lits (yals, (CIDX)); \
  if (!yals->opts.logging.val) break; \
  yals_log_start (yals, ##ARGS); \
  fprintf (yals->out, " cardinality constraint %d :", (CIDX)); \
  for (P = (LITS); *P; P++) \
    fprintf (yals->out, " %d", *P); \
  yals_log_end (yals); \
} while (0)
#else
#define LOG(ARGS...) do { } while (0)
#define LOGLITS(ARGS...) do { } while (0)
#define LOGCIDX(ARGS...) do { } while (0)
#define LOGCARDCIDX(ARGS...) do { } while (0)
#endif

static void yals_msglock (Yals * yals) {
  if (yals->cbs.msg.lock) yals->cbs.msg.lock (yals->cbs.msg.state);
}

static void yals_msgunlock (Yals * yals) {
  if (yals->cbs.msg.unlock) yals->cbs.msg.unlock (yals->cbs.msg.state);
}

#ifndef NDEBUG

static void yals_log_start (Yals * yals, const char * fmt, ...) {
  va_list ap;
  yals_msglock (yals);
  assert (yals->opts.logging.val);
  fputs ("c [LOGYALS] ", yals->out);
  va_start (ap, fmt);
  vfprintf (yals->out, fmt, ap);
  va_end (ap);
}

static void yals_log_end (Yals * yals) {
  (void) yals;
  assert (yals->opts.logging.val);
  fputc ('\n', yals->out);
  fflush (yals->out);
  yals_msgunlock (yals);
}

#endif

static inline void yals_abort (Yals * yals, const char * fmt, ...) {
  va_list ap;
  yals_msglock (yals);
  fflush (yals->out);
  fprintf (stderr, "%s*** libyals abort: ", yals->opts.prefix);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  yals_msgunlock (yals);
  abort ();
}

static inline void yals_exit (Yals * yals, int exit_code, const char * fmt, ...) {
  va_list ap;
  yals_msglock (yals);
  fflush (yals->out);
  fprintf (stderr, "%s*** libyals exit: ", yals->opts.prefix);
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  yals_msgunlock (yals);
  exit (exit_code);
}

static inline void yals_warn (Yals * yals, const char * fmt, ...) {
  va_list ap;
  yals_msglock (yals);
  fprintf (yals->out, "%sWARNING ", yals->opts.prefix);
  va_start (ap, fmt);
  vfprintf (yals->out, fmt, ap);
  va_end (ap);
  fputc ('\n', yals->out);
  fflush (yals->out);
  yals_msgunlock (yals);
}
static inline void yals_msg (Yals * yals, int level, const char * fmt, ...) {
  va_list ap;
  if (level > 0 && (!yals || yals->opts.verbose.val < level)) return;
  yals_msglock (yals);
  fprintf (yals->out, "%s", yals->opts.prefix);
  va_start (ap, fmt);
  vfprintf (yals->out, fmt, ap);
  va_end (ap);
  fputc ('\n', yals->out);
  fflush (yals->out);
  yals_msgunlock (yals);
}

/*------------------------------------------------------------------------*/

static inline double yals_avg (double a, double b) { return b ? a/b : 0; }

static inline double yals_pct (double a, double b) { return b ? 100.0 * a / b : 0; }

static inline double yals_process_time () {
  struct rusage u;
  double res;
  if (getrusage (RUSAGE_SELF, &u)) return 0;
  res = u.ru_utime.tv_sec + 1e-6 * u.ru_utime.tv_usec;
  res += u.ru_stime.tv_sec + 1e-6 * u.ru_stime.tv_usec;
  return res;
}

static inline double yals_time (Yals * yals) {
  if (yals && yals->cbs.time) return yals->cbs.time ();
  else return yals_process_time ();
}

// Per-phase profiling timer. Returns 0 unless verbose printing is enabled,
// skipping the getrusage syscall in production (verbose=0) runs. The
// stats.{maxs_time,time.restart} fields it populates are only consumed by
// yals_print_stats (at verbose>=0, they'll just print as 0.00 seconds when
// the syscall was skipped). At ~14-18% of CPU in profiles before this gate,
// it was the largest non-algorithmic cost.
static inline double yals_time_phase (Yals * yals) {
  if (yals->opts.verbose.val == 0) return 0.0;
  return yals_time (yals);
}

static void yals_flush_time (Yals * yals) {
  double time, entered;
#ifdef __GNUC__
  int old;
  // begin{atomic}
  old = __sync_val_compare_and_swap (&yals->stats.flushing_time, 0, 42);
  assert (old == 0 || old == 42);
  if (old) return;
  //
  // TODO I still occasionally have way too large kflips/sec if interrupted
  // and I do not know why?  Either there is a bug in flushing or there is
  // still a data race here and I did not apply this CAS sequence correctly.
  //
#endif
  time = yals_time (yals);
  entered = yals->stats.time.entered;
  yals->stats.time.entered = time;
  assert (time >= entered);
  time -= entered;
  yals->stats.time.total += time;
#ifdef __GNUC__
  old = __sync_val_compare_and_swap (&yals->stats.flushing_time, 42, 0);
  assert (old == 42);
  (void) old;
  // end{atomic}
#endif
}

static inline double yals_sec (Yals * yals) {
  yals_flush_time (yals);
  return yals->stats.time.total;
}

/*------------------------------------------------------------------------*/

static inline void yals_inc_allocated (Yals * yals, size_t bytes) {
  yals->stats.allocated.current += bytes;
  if (yals->stats.allocated.current > yals->stats.allocated.max)
    yals->stats.allocated.max = yals->stats.allocated.current;
}

static inline void yals_dec_allocated (Yals * yals, size_t bytes) {
  assert (yals->stats.allocated.current >= bytes);
  yals->stats.allocated.current -= bytes;
}

static inline void * yals_malloc (Yals * yals, size_t bytes) {
  void * res;
  if (!bytes) return 0;
  res = yals->mem.malloc (yals->mem.mgr, bytes);
  if (!res) yals_abort (yals, "out of memory in 'yals_malloc'");
  yals_inc_allocated (yals, bytes);
  memset (res, 0, bytes);
  return res;
}

static inline void yals_free (Yals * yals, void * ptr, size_t bytes) {
  assert (!ptr == !bytes);
  if (!ptr) return;
  yals_dec_allocated (yals, bytes);
  yals->mem.free (yals->mem.mgr, ptr, bytes);
}

static inline void * yals_realloc (Yals * yals, void * ptr, size_t o, size_t n) {
  char * res;
  assert (!ptr == !o);
  if (!n) { yals_free (yals, ptr, o); return 0; }
  if (!o) return yals_malloc (yals, n);
  yals_dec_allocated (yals, o);
  res = yals->mem.realloc (yals->mem.mgr, ptr, o, n);
  if (n && !res) yals_abort (yals, "out of memory in 'yals_realloc'");
  yals_inc_allocated (yals, n);
  if (n > o) memset (res + o, 0, n - o);
  return res;
}

static inline size_t yals_max_allocated (Yals * yals) {
  return yals->stats.allocated.max;
}

/*------------------------------------------------------------------------*/

static inline char * yals_strdup (Yals * yals, const char * str) {
  assert (str);
  return strcpy (yals_malloc (yals, strlen (str) + 1), str);
}

static inline void yals_strdel (Yals * yals, char * str) {
  assert (str);
  yals_free (yals, str, strlen (str) + 1);
}

/*------------------------------------------------------------------------*/

static inline void yals_srand (Yals * yals, unsigned long long seed) {
  unsigned z = seed >> 32, w = seed;
  if (!z) z = ~z;
  if (!w) w = ~w;
  yals->rng.z = z, yals->rng.w = w;
  yals_msg (yals, 2, "setting random seed %llu", seed);
}

static inline unsigned yals_rand (Yals * yals) {
  unsigned res;
  yals->rng.z = 36969 * (yals->rng.z & 65535) + (yals->rng.z >> 16);
  yals->rng.w = 18000 * (yals->rng.w & 65535) + (yals->rng.w >> 16);
  res = (yals->rng.z << 16) + yals->rng.w;
  return res;
}

static inline unsigned yals_rand_mod (Yals * yals, unsigned mod) {
  unsigned res;
  assert (mod >= 1);
  if (mod <= 1) return 0;
  res = yals_rand (yals);
  res %= mod;
  return res;
}

/*------------------------------------------------------------------------*/





static inline int * yals_lits (Yals * yals, int cidx) {
  INC (lits);
  assert_valid_cidx (cidx);
  return yals->cdb.start + yals->lits[cidx];
}

/*
  Cardinality constraints are stored in card_cdb in sequence 
  as bound, lits, 0, ...
  
  e.g. x_1 + x_2 + x_3 >= 2

  2 x_1 x_2 x_3 0

*/

// return a pointer to the literals of a cardinality constraint
static inline int * yals_card_lits (Yals * yals, int cidx) {
  INC (lits); // incrementing lits access?
  assert_valid_card_cidx (cidx);
  return yals->card_cdb.start + yals->card_lits[cidx] + 1; // +1 to avoid bound
}

// return the bound for a cardinality constraint
static inline int yals_card_bound (Yals * yals, int cidx) {
  INC (lits);
  assert_valid_card_cidx (cidx);
  return *(yals->card_cdb.start + yals->card_lits[cidx]); 
}

/*
  Get length of a cardinality constraint

  Initially we looped through literals to count the length.
  Now we store the length in card_size for constant lookup.
*/
static inline int yals_card_length (Yals * yals, int cidx) {
  // int length = 0;
  // int * p;

  // INC (lits); // incrementing lits access?
  // assert_valid_cidx (cidx);

  // p = yals->card_cdb.start + yals->card_lits[cidx] + 1;
  // while (*p) length++;
  // return length; 

  return PEEK (yals->card_size, cidx);
}

/*
  Provide pointers used for iterating over the satisfied literals of a
  partitioned cardinality constraint.

  begin points at first literal, break loop whne begin == end
*/
static inline void yals_card_sat_iters (Yals *yals, int cidx, int **begin, int **end) {
  assert_valid_card_cidx (cidx);

  *begin = yals_card_lits (yals, cidx);
  *end = *begin + yals->ddfw.card_sat_count_in_clause[cidx];
}

/*
  Provide pointers used for iterating over the falsified literals of a
  partitioned cardinality constraint.

  begin points at first literal, break loop whne begin == end
*/
static inline void yals_card_unsat_iters (Yals *yals, int cidx, int **begin, int **end) {
  assert_valid_card_cidx (cidx);

  *begin = yals_card_lits (yals, cidx) + yals->ddfw.card_sat_count_in_clause [cidx];
  *end = yals_card_lits (yals, cidx) + yals_card_length (yals, cidx);
}

// wrapper for weight updates
// needed in order to account for changes in the heap
static inline void yals_ddfw_update_var_weight (Yals *yals, int lit, int soft, int sat, double weight_change) {
  double *weights;
  STACK_INT *uvars;
  int * pos;
  int var = ABS(lit);
  uvars = &yals->ddfw.uvars_changed;
  pos = yals->ddfw.uvar_changed_pos;
  if (soft) {
    if (sat)
      weights = yals->ddfw.sat1_weights_soft;
    else 
      weights = yals->ddfw.unsat_weights_soft;
  } else {
    if (sat)
      weights = yals->ddfw.sat1_weights;
    else 
      weights = yals->ddfw.unsat_weights;
  }

  LOG ("weight update of %lf for lit %d with sat %d and soft %d", weight_change, lit, sat, soft);

  // Independent weighting of positive vs negative constraints: scale the
  // falsified-weight (sat==0) contribution of POSITIVE constraints by
  // pos = paramPos/1000. For pure-polarity formulas (e.g. ntil) the sign of
  // the updated literal equals the polarity of the source constraint, so
  // lit>0 in the unsat-weight path means a positive constraint. Both the
  // initial population and every incremental make/break/transfer flow through
  // here, so the scaling stays consistent (no drift). No-op when paramPos=1000.
  if (sat == 0 && lit > 0 && yals->opts.paramPos.val != 1000)
    weight_change = weight_change * (double) yals->opts.paramPos.val / 1000.0;

  weights[get_pos (lit)] += weight_change;

  // if (soft && !weights[get_pos (lit)] && yals->ddfw.var_unsat_count_soft[abs(lit)]) {
  //   exit (1);
  // } happens after

  if (pos[var] < 0) { // add to changed stack
    // pos[var] = COUNT (uvars);
    pos[var] = 1;
    PUSH (*uvars, var);
    LOG ("Pushed %d", var);
  }
}

#endif
