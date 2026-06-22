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
#include <pthread.h> // palsat workers share one YalsFormula via a build barrier

#if defined(__linux__)
#include <fpu_control.h> // Set FPU to double precision on Linux.
#endif


/*------------------------------------------------------------------------*/

#define STRATSTEMPLATE \
  STRAT (pol,1);

#define STRAT(NAME,ENABLED) int NAME

/*------------------------------------------------------------------------*/

typedef void * (*YalsMalloc)(void*,size_t);
typedef void * (*YalsRealloc)(void*,void*,size_t,size_t);
typedef void (*YalsFree)(void*,void*,size_t);

#define TYPECLAUSE 0
#define TYPECARDINALITY 1


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

  int64_t flips, bzflips, hits, unsum, get_random_sat_cnt, get_random_sat_missed;
  // Value of `flips` at the start of the current probe (the last time this
  // worker began from a freshly picked assignment). Used to report how many
  // flips a probe needed to reach the global best score.
  int64_t probe_start_flips;
  // 1 iff the current probe started from a freshly generated random
  // assignment (not a best/keep/all-polarity pick). Only random-started
  // probes contribute to the global-best tracker.
  int probe_random;
  struct {
    struct { int64_t count; } outer;
    struct { int64_t count; } inner;
    int64_t bypassed;  // # times --bypass extended a probe past cutoff
  } restart;
  struct { struct { int chunks, lnks; } max; int64_t unfair; } queue;
  struct { int64_t def, rnd; } strat;
  struct { int64_t best, keep, pos, neg, rnd; } pick;
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
typedef struct WT {

  LitClauses* lit_clauses_map;
 
  /** Whole neighborhood for all the clauses **/

  int neighbourhood_at_init;
  /** On demand neighborhood for a clause **/

  int prev_unsat_weights;
 
 
  double * clause_weights; // wt weight of each clause
  double * unsat_weights; // wt weight gain for flipping lit (unsat to sat)
  double * sat1_weights; // wt weight lost for flipping lit (sat to unsat)
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

  int active;
  int recent_max_reduction;
  int flip_span;
  int prob_check_window;
  int alg_switch;

  double time_wt;
  int flips_temp, flips_wt;

  double sum_uwr;
  double clsselectp;
  double wtstartth;
  int guaranteed_uwrvs, missed_guaranteed_uwvars;
  unsigned source_not_selected;
  unsigned total_transfers;

  heap uvars_heap; // heap for variables in falsified constraints

  /*
    additional data for cardinality constraint handling
  */

  STACK (int) card_helper_hash_changed_idx;
  int * card_helper_hash_clauses;
  int * card_sat_count_in_clause;
  int * card_sat_dirty; // 1 iff the sat/unsat partition may have drifted while over-satisfied (needs a full re-sort on re-entry to critical)
  double * card_weights; // cardinality constraint wt weights

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
  // Epoch stamps: a bulk weight reset bumps topk_epoch in O(1) to invalidate
  // every list at once. A list p is STALE iff topk_gen[p] != topk_epoch; its
  // count/list/pos are frozen-but-self-consistent (pre-reset) and its weights
  // are stale, so maintenance hooks SKIP it and yals_topk_best rebuilds it
  // lazily on first access (rebuild_lit restamps gen = epoch). This defers the
  // per-list bubble work to only the literals a probe actually queries.
  unsigned topk_epoch;             // current generation; bumped on bulk reset
  unsigned * topk_gen;             // [nlits] per-list generation stamp
  double * nbr_w;    // [E] edge -> cached weight of nbr_con[e]; kept in sync on every weight change so yals_nbr_better avoids the nbr_con indirection + clause/card branch per comparison
  // Diagnostics (printed by yals_print_stats when --topk>0).
  int64_t topk_stat_q;             // total yals_topk_best queries
  int64_t topk_stat_rebuild;       // queries that triggered an empty-list rebuild
  int64_t topk_stat_eligible;      // queries that returned an eligible source
  int64_t topk_stat_no_eligible;   // queries that returned -1 (caller falls through to scan)
  int64_t topk_stat_walked;        // sum of positions visited across all queries (sum of 1..count for each query)
  int64_t topk_stat_diverged;      // (TOPK_VERIFY=1 env var) queries where top-K pick != full-scan pick
  int topk_verify;                 // set from TOPK_VERIFY env at build time

  // --wsamplepow: segment sum-tree over the wt weight of every constraint
  // (unified id: clause u<nclauses; else card u-nclauses). Leaf u holds the
  // raw wt weight; internal nodes hold subtree sums; tree[1] = total. Drawn
  // proportional to weight in O(log N); a single weight change updates one
  // leaf-to-root path. Satisfaction is NOT encoded here (the caller
  // rejection-filters drawn sources for SAT / min-weight / hard-soft).
  int wsample_built;
  int wsample_N;          // real leaves = nclauses + card_nclauses
  int wsample_M;          // tree base = next power of two >= N
  double * wsample_tree;  // [2*M] segment tree (index 1 = root = total)

  // Per-variable last-flip step number (stats.flips value at the moment v
  // was last flipped). Used by:
  //   - --tabu: v is tabu while stats.flips - last_flipped[v] < opts.tabu.val
  //   - avg-age stat in "new minimum" prints
  // Always allocated when WT is built. Indexed by variable id (1..nvars).
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

  // Per-probe best-score log. A "probe" is the work between consecutive
  // inner restarts: from yals_pick_assignment to the next cutoff. Each
  // entry is stats.tmp at the *end* of a
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

} WT;

// structure for stack constaining falsified constraints,
// also stores the weight of falsified constraints in the stack
typedef struct UNSAT_STACK {
  int usequeue; int hard_cnt; Queue queue; STACK_INT stack;
} UNSAT_STACK;

// Read-only formula data: built once during parsing and yals_connect /
// yals_card_connect, then immutable for the rest of the search. Factored out
// of Yals so a single copy can be shared across all palsat worker threads --
// each Yals points its 'f' at the same YalsFormula.
typedef struct YalsFormula {
  // clause database
  STACK(int) cdb;                 // clause literals, 0-separated
  int * lits;                     // clause cidx -> offset into cdb
  int * occs, noccs;              // occurrence lists + total size
  int * refs;                     // literal -> offset into occs
  STACK(int) clause_size;         // clause cidx -> length
  // cardinality index (the card_cdb literal array itself is NOT here: the
  // solver reorders literals within each constraint in place during search,
  // so card_cdb must stay per-thread -- it lives in Yals below). These index
  // arrays only depend on which literals occur in which constraint, not their
  // order, so they remain shared and read-only.
  int * card_lits, * card_refs;
  int * card_occs, card_noccs;
  STACK(int) card_size;
  // Forced assignment derived during parsing + preprocessing (the trail after
  // unit propagation). Read-only after the formula is built; every worker seeds
  // its set/clear masks from this, so it is shared along with the clause DB.
  STACK(int) forced;
  // One-shot build barrier. In shared mode only the owning worker builds the
  // arrays above; the others block on this until 'built' is set. In non-shared
  // mode each worker owns its own YalsFormula and signals it harmlessly.
  pthread_mutex_t build_lock;
  pthread_cond_t build_cond;
  int built;
} YalsFormula;

// structure for solver
typedef struct Yals {
  RNG rng;
  FILE * out;
  UNSAT_STACK unsat; // falsified constraints
  YalsFormula * f; // shared read-only formula data (see YalsFormula above)
  int owns_formula; // 1 if this worker built and owns *f (frees it); 0 if it
                    // merely shares another worker's *f (read-only)
  // Cardinality clause DB (bound, literals, 0, ...). Per-thread, NOT in the
  // shared *f: the solver reorders literals within each constraint in place
  // during search (yals_card_sort_sat / incsatcnt partition moves), so every
  // worker needs its own mutable copy. The card index arrays in *f stay shared.
  STACK(int) card_cdb;
  int nvars; int64_t * flips;
  STACK(signed char) mark;
  int trivial, mt, pick;
  Word * vals, * best, * tmp, * clear, * set, *curr; int nvarwords;
  STACK(int) trail, phases, clause;
  int satcntbytes; union { U1 * satcnt1; U2 * satcnt2; U4 * satcnt4; };
  int * pos; Lnk ** lnk;
  int * crit;
  int nclauses, nbin, ntrn, minlen, maxlen; double avglen;
  STACK(unsigned) breaks; STACK(double) scores; STACK(int) cands;
  STACK(int) minlits;
  Callbacks cbs;
  Limits limits;
  Strat strat;
  Stats stats;
  Opts opts;
  Mem mem;
  FPU fpu;
  Exp exp;
  WT wt;
  int wid;
  int consecutive_non_improvement, last_flip_unsat_count;

  STACK (Lit_Score) lit_scores;

  /*
    additional data for cardinality constraint handling
  */
  UNSAT_STACK card_unsat; // falsified hard (all) constraints

  int card_crit;

  int bound, card_nclauses;

  double card_avglen;

  int * card_pos; // Lnk ** card_lnk; // Only stack currently

  int card_minlen, card_maxlen;
  int card_satcntbytes; union { U1 * card_satcnt1; U2 * card_satcnt2; U4 * card_satcnt4; };
  // int ** card_crit; // critical literals for a cardinality constraint

  YalsProbePool * probe_pool;

} Yals;

/*------------------------------------------------------------------------*/

Yals * yals_new ();
void yals_del (Yals *);

/*------------------------------------------------------------------------*/



Yals * yals_new_with_mem_mgr (void*, YalsMalloc, YalsRealloc, YalsFree);

/*------------------------------------------------------------------------*/

// palsat shared-formula support. After the formula has been parsed into a
// single owner worker, 'yals_prepare_shared_formula' simplifies it once
// (unit propagation, if enabled) and captures the resulting forced assignment
// into the owner's YalsFormula. Returns 20 if the formula is already
// unsatisfiable (empty clause), else 0. 'yals_share_formula' then points a
// non-owner worker at the owner's formula so a single copy is shared.
int yals_prepare_shared_formula (Yals * owner);
void yals_share_formula (Yals * dst, Yals * src);

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
// Each worker's per-probe scores (yals->wt.probe_bests) are merged
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



unsigned yals_satcnt (Yals * yals, int cidx);

void yals_add_vars_to_uvars (Yals* yals, int cidx, int constraint_type);
void yals_delete_vars_from_uvars (Yals* yals, int cidx, int constraint_type);

void yals_flip_value_of_lit (Yals * yals, int lit);
void yals_make_clauses_after_flipping_lit (Yals * yals, int lit);
void yals_break_clauses_after_flipping_lit (Yals * yals, int lit);
void yals_update_sat_and_unsat (Yals * yals);

int yals_pick_literal_from_heap (Yals * yals);

void yals_update_score_function_weights (Yals * yals);

void yals_remove_trailing_bits (Yals * yals);
void yals_set_units (Yals * yals);

void yals_update_changed_var_weights (Yals * yals);

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
  do { assert (0 <= OCCS), assert (OCCS < yals->f->noccs); } while (0)

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
  do { assert (0 <= OCCS), assert (OCCS < yals->f->card_noccs); } while (0)

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
  assert (yals->f->refs);
  return yals->f->refs + 2*idx + (lit < 0);
}

static inline int * yals_card_refs (Yals * yals, int lit) {
  int idx = ABS (lit);
  assert_valid_idx (idx);
  assert (yals->f->card_refs);
  return yals->f->card_refs + 2*idx + (lit < 0);
}

static inline int * yals_occs (Yals * yals, int lit) {
  int occs;
  INC (occs);
  occs = *yals_refs (yals, lit);
  assert_valid_occs (occs);
  return yals->f->occs + occs;
}

static inline int * yals_card_occs (Yals * yals, int lit) {
  int occs;
  INC (occs);
  occs = *yals_card_refs (yals, lit);
  assert_valid_card_occs (occs);
  return yals->f->card_occs + occs;
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
// stats.time.restart field it populates is only consumed by
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
  return yals->f->cdb.start + yals->f->lits[cidx];
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
  return yals->card_cdb.start + yals->f->card_lits[cidx] + 1; // +1 to avoid bound
}

// return the bound for a cardinality constraint
static inline int yals_card_bound (Yals * yals, int cidx) {
  INC (lits);
  assert_valid_card_cidx (cidx);
  return *(yals->card_cdb.start + yals->f->card_lits[cidx]);
}

/*
  Get length of a cardinality constraint

  Initially we looped through literals to count the length.
  Now we store the length in card_size for constant lookup.
*/
static inline int yals_card_length (Yals * yals, int cidx) {

  // INC (lits); // incrementing lits access?


  return PEEK (yals->f->card_size, cidx);
}

/*
  Provide pointers used for iterating over the satisfied literals of a
  partitioned cardinality constraint.

  begin points at first literal, break loop whne begin == end
*/
static inline void yals_card_sat_iters (Yals *yals, int cidx, int **begin, int **end) {
  assert_valid_card_cidx (cidx);

  *begin = yals_card_lits (yals, cidx);
  *end = *begin + yals->wt.card_sat_count_in_clause[cidx];
}

/*
  Provide pointers used for iterating over the falsified literals of a
  partitioned cardinality constraint.

  begin points at first literal, break loop whne begin == end
*/
static inline void yals_card_unsat_iters (Yals *yals, int cidx, int **begin, int **end) {
  assert_valid_card_cidx (cidx);

  *begin = yals_card_lits (yals, cidx) + yals->wt.card_sat_count_in_clause [cidx];
  *end = yals_card_lits (yals, cidx) + yals_card_length (yals, cidx);
}

// wrapper for weight updates
// needed in order to account for changes in the heap
static inline void yals_update_var_weight (Yals *yals, int lit, int sat, double weight_change) {
  double *weights;
  STACK_INT *uvars;
  int * pos;
  int var = ABS(lit);
  uvars = &yals->wt.uvars_changed;
  pos = yals->wt.uvar_changed_pos;
  if (sat)
    weights = yals->wt.sat1_weights;
  else
    weights = yals->wt.unsat_weights;

  LOG ("weight update of %lf for lit %d with sat %d", weight_change, lit, sat);

  weights[get_pos (lit)] += weight_change;

  if (pos[var] < 0) { // add to changed stack
    pos[var] = 1;
    PUSH (*uvars, var);
    LOG ("Pushed %d", var);
  }
}

#endif
