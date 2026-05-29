/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#include "yals.h"

/*------------------------------------------------------------------------*/

#define YALSINTERNAL
#include "yils_card.h"
#include "inlineheap.h"
#include "stack.h"
#include "invariants.h"
#include "queue.h"
#include "propagate.h"
#include "maxsat.h"
#include "pure_maxsat.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <float.h>
#include <pthread.h>
#include <sys/resource.h>
#include <sys/time.h>



/*------------------------------------------------------------------------*/

void yals_set_fpu (Yals * yals) {
#ifdef __linux__
  fpu_control_t control;
  _FPU_GETCW (yals->fpu.control);
  control = yals->fpu.control;
  control &= ~_FPU_EXTENDED;
  control &= ~_FPU_SINGLE;
  control |= _FPU_DOUBLE;
  _FPU_SETCW (control);
  yals_msg (yals, 1, "set FPU mode to use double precision");
#endif
  yals->fpu.saved = 1;
}

void yals_reset_fpu (Yals * yals) {
  (void) yals;
  assert (yals->fpu.saved);
#ifdef __linux__
  _FPU_SETCW (yals->fpu.control);
  yals_msg (yals, 1, "reset FPU to original double precision mode");
#endif
}

/*------------------------------------------------------------------------*/

enum ClausePicking {
  PSEUDO_BFS_CLAUSE_PICKING = -1,
  RANDOM_CLAUSE_PICKING = 0,
  BFS_CLAUSE_PICKING = 1,
  DFS_CLAUSE_PICKING = 2,
  RELAXED_BFS_CLAUSE_PICKING = 3,
  UNFAIR_BFS_CLAUSE_PICKING = 4,
};


/*------------------------------------------------------------------------*/

#define WEIGHT_MAX 9999999.0 // largest ddfw weight allowed for soft constraints
#define HARD_WEIGHT_MAX 999999999999.0 // largest ddfw weight allowed for hard constraints (factor 100,000 bigger than soft)

static int ndone; 
static int card_ndone; 

/*------------------------------------------------------------------------*/

const char * yals_default_prefix () { return YALS_DEFAULT_PREFIX; }

/*------------------------------------------------------------------------*/


// polarity of literal in best solution
static inline int yals_best (Yals * yals, int lit) {
  int idx = ABS (lit), res = !GETBIT (yals->best, yals->nvarwords, idx);
  if (lit > 0) res = !res;
  return res;
}


/*------------------------------------------------------------------------*/
// Weighted break score API used in probSAT
// This would be used for a fast descent

// These functions should not be called when in ddfw mode
// i.e., !yals->ddfw.ddfw_active


static void yals_inc_weighted_break (Yals * yals, int lit, int len) {
  //double s = yals_time (yals);
  int idx = ABS (lit), pos;
  unsigned w;
  assert (yals->crit);
  assert_valid_idx (idx);
  assert_valid_len (len);
  pos = 2*idx + (lit < 0);
  w = yals->weights[len]; // TODO avoid mem if uniform
  yals->weightedbreak[pos] += w;
  assert (yals->weightedbreak[pos] >= w);
  INC (weight);
  //yals->ddfw.init_neighborhood_time += yals_time (yals) - s; 
}

// TODO merge these functions and simply call with clause type as additional argument
// increment a single literal break weight
static void yals_card_inc_weighted_break (Yals * yals, int lit, int len) {
  int idx = ABS (lit), pos;
  unsigned w;
  assert (yals->crit);
  assert_valid_idx (idx);
  assert_valid_card_len (len);
  pos = 2*idx + (lit < 0);
  w = yals->weights[len]; // TODO avoid mem if uniform
  yals->weightedbreak[pos] += w;
  assert (yals->weightedbreak[pos] >= w);
  INC (weight);
}

/*
  Every falsified literal carries weight of cardinality constraint.
  This is true when the constraint is falsified. 
*/
static void yals_card_inc_all_weighted_break (Yals * yals, int cidx, int len) {
  //double s = yals_time (yals);
  int *begin, *end;
  yals_card_sat_iters (yals, cidx, &begin, &end);
  // yals_msg (yals, 5, "satcnt for sat_iters %d cidx %d begin %d", yals_card_satcnt (yals, cidx), cidx, *begin);

  yals_msg (yals, 4, "init weight %d cidx %d", *begin, cidx);

  for (; begin != end; begin++) {
    yals_msg (yals, 4, "init weight %d cidx %d pointer %p", *begin, cidx, begin);
    yals_card_inc_weighted_break (yals, *begin, len); 
  }
}

static void yals_dec_weighted_break (Yals * yals, int lit, int len) {
  //double s = yals_time (yals);
  int idx = ABS (lit), pos;
  unsigned w;
  assert (yals->crit);
  assert_valid_idx (idx);
  assert_valid_len (len);
  pos = 2*idx + (lit < 0);
  w = yals->weights[len]; // TODO avoid mem if uniform
  assert (yals->weightedbreak[pos] >= w);
  yals->weightedbreak[pos] -= w;
  INC (weight);
  //yals->ddfw.init_neighborhood_time += yals_time (yals) - s;
}

// decrement a single literal
static void yals_card_dec_weighted_break (Yals * yals, int lit, int len) {
  //double s = yals_time (yals);
  int idx = ABS (lit), pos;
  unsigned w;
  assert (yals->crit);
  assert_valid_idx (idx);
  assert_valid_card_len (len);
  pos = 2*idx + (lit < 0);
  w = yals->weights[len]; // TODO avoid mem if uniform
  assert (yals->weightedbreak[pos] >= w);
  yals->weightedbreak[pos] -= w;
  INC (weight);
  //yals->ddfw.init_neighborhood_time += yals_time (yals) - s;
}

// decrement a single literal
static void yals_card_dec_all_weighted_break (Yals * yals, int cidx, int len, int avoid_lit) {
  int *begin, *end;
  yals_card_sat_iters (yals, cidx, &begin, &end);
  for (; begin != end; begin++)
    yals_card_dec_weighted_break (yals, *begin, len); 
}

/*------------------------------------------------------------------------*/

// number of satisfied literals in a clause
unsigned yals_satcnt (Yals * yals, int cidx) {
  assert_valid_cidx (cidx);
  //return yals->ddfw.sat_count_in_clause [cidx];
  if (yals->satcntbytes == 1) return yals->satcnt1[cidx];
  if (yals->satcntbytes == 2) return yals->satcnt2[cidx];
  return yals->satcnt4[cidx];
}

static void yals_setsatcnt (Yals * yals, int cidx, unsigned satcnt) {
  assert_valid_cidx (cidx);
  if (yals->satcntbytes == 1) {
    assert (satcnt < 256);
    yals->satcnt1[cidx] = satcnt;
  } else if (yals->satcntbytes == 2) {
    assert (satcnt < 65536);
    yals->satcnt2[cidx] = satcnt;
  } else {
    yals->satcnt4[cidx] = satcnt;
  }
}

// number of satisfied literals in a cardinality constraints
unsigned yals_card_satcnt (Yals * yals, int cidx) {
  assert_valid_card_cidx (cidx);
  //return yals->ddfw.sat_count_in_clause [cidx]; 
  if (yals->card_satcntbytes == 1) return yals->card_satcnt1[cidx];
  if (yals->card_satcntbytes == 2) return yals->card_satcnt2[cidx];
  return yals->card_satcnt4[cidx];
}

static void yals_card_setsatcnt (Yals * yals, int cidx, unsigned satcnt) {
  assert_valid_card_cidx (cidx);
  if (yals->card_satcntbytes == 1) {
    assert (satcnt < 256);
    yals->card_satcnt1[cidx] = satcnt;
  } else if (yals->card_satcntbytes == 2) {
    assert (satcnt < 65536);
    yals->card_satcnt2[cidx] = satcnt;
  } else {
    yals->card_satcnt4[cidx] = satcnt;
  }
}


/*
  Sort a cardinality constraint based on satisfied and falsified literals.
  Satisfied literals come first, from 0 to nsat-1, then nsat-1 to length-1 are falsified.

  We sort so that it is easier to determine which literals should accumulate 
  ddfw weight. Falsified literals within a constraint need to be known to 
  sum the weight-change of a variable.

  Only need to sort if constraint is critical or falsified,
  otherwise there is no ddfw weight change to consider.
*/
void yals_card_sort_sat (Yals *yals, int cidx) {
  int *front, *back, *lits;
  int nsat;

  assert_valid_card_cidx (cidx);

  nsat = yals->ddfw.card_sat_count_in_clause [cidx];
  front = lits = yals_card_lits (yals, cidx);
  back  = lits + yals_card_length (yals, cidx) -1;

  yals_msg (yals, 4, "Sort front %d back %d nsat %d",*front, *back, nsat );

  while (front != back) {
    if (yals_val (yals, *front)) { // sat in front, incremenet
      front++;
    } else if (!yals_val (yals, *back)) { // falsified in back, decrement
      back--;
    } else { // need to swap
      SWAP (int, *front, *back);
      front++;
      if (front == back) break; // check break condition
      back--;
    }
  }

  if (yals_val (yals, *front)) front++; // case where all lits are satisfied

  LOGCARDCIDX (cidx, "critical, finished sorting");

  assert (nsat == (front-lits));

}

/*
  get position of lit within cardinality constraint starting at pos
*/
static inline int * yals_card_lit_pos (Yals *yals, int* lits, int lit) {
  while (*lits != lit) lits++;
  return lits;
}

/*
  lit has become sat, move to correct partition of cardinality constraint

  Assumes nsat has been updated before call
*/
void yals_card_new_sat (Yals *yals, int cidx, int lit) {
  int *pos, *lits;
  int nsat;

  assert_valid_card_cidx (cidx);

  nsat = yals->ddfw.card_sat_count_in_clause [cidx];
  lits = yals_card_lits (yals, cidx);
  pos = yals_card_lit_pos (yals, lits+nsat-1, lit);
  
  SWAP (int, lits[nsat-1], *pos);

}

/*
  lit has become falsified, move to correct partition of cardinality constraint

  Assumes nsat has been updated before call
*/
void yals_card_new_unsat (Yals *yals, int cidx, int lit) {
  int *pos, *lits;
  int nsat;

  assert_valid_card_cidx (cidx);

  nsat = yals->ddfw.card_sat_count_in_clause [cidx];
  lits = yals_card_lits (yals, cidx);
  pos = yals_card_lit_pos (yals, lits, lit);
  
  SWAP (int, lits[nsat], *pos);

}

// recently flipped literal is now true with this clause
// update weighted break if necessary, udpate satcnt, update critical literal
// return true is clause is not made (already sat)
static unsigned yals_incsatcnt (Yals * yals, int cidx, int lit, int len) {
  unsigned res;
  assert_valid_cidx (cidx);
  assert_valid_len (len);
  res = yals_satcnt (yals, cidx);
  yals_setsatcnt (yals, cidx, res+1);

  yals->ddfw.sat_count_in_clause [cidx] = res+1;
  //printf ("\n===> inc %d %d",res, PEEK(yals->clause_size, cidx));
#ifndef NYALSTATS
  assert (res + 1 <= yals->maxlen);
  yals->stats.inc[res]++;
#endif
  if (yals->crit) {
    if (!yals->ddfw.ddfw_active)
    {
      if (res == 1) yals_dec_weighted_break (yals, yals->crit[cidx], len); // no longer critical
      else if (!res) yals_inc_weighted_break (yals, lit, len); // now critical
    }
    yals->crit[cidx] ^= lit;
    assert (res || yals->crit[cidx] == lit);
  }
  return res;
}

/*

  Note: no ddfw weights updated here because this is called directly by
    probSAT. We only update ddfw weights in the ddfw helper function that calls
    this.

  One additional literal in the cardinality constraint becomes true

  Let nsat be the number of satisfied literals before the flip, such that the
  updated number of satisfied literals is nsat +1

  Three cases:

  1) oldnsat > bound : overly satisifed
    - nothing to do, already no value being added from this clause
  2) oldnsat = bound : overly satisfied and no longer critical
    - remove critical weights from the break weight
    - not new lit!
  3) oldnsat < bound : falsified or critically satisfied
    - add new lit to the critical weights as a break lit


  result : true if clause is not made (already sat)

*/
static unsigned yals_card_incsatcnt (Yals * yals, int cidx, int lit, int len) {
  unsigned res;
  int bound, oldnsat;
  assert_valid_card_cidx (cidx);
  assert_valid_card_len (len);
  res = yals_card_satcnt (yals, cidx);
  yals_card_setsatcnt (yals, cidx, res+1);

  LOGCARDCIDX (cidx, "new satcnt %d ", yals_card_satcnt (yals, cidx));

  oldnsat = res;

  yals->ddfw.card_sat_count_in_clause [cidx] = (int) res+1;
  //printf ("\n===> inc %d %d",res, PEEK(yals->clause_size, cidx));
// #ifndef NYALSTATS
//   assert (res + 1 <= yals->card_maxlen);
//   yals->stats.inc[res]++;
// #endif
  if (yals->card_crit) {
    bound = yals_card_bound (yals, cidx);
    if (!yals->ddfw.ddfw_active)
    { 
      if (oldnsat == bound) { // 2) remove weights 
        yals_card_dec_all_weighted_break (yals, cidx, len, lit);
      } else if ( oldnsat < bound ) { // 3) add weight of new literal
        yals_card_inc_weighted_break (yals, lit, len);
      }
    }
    if ( res <= bound ) { // add new lit to correct position
      yals_card_new_sat (yals, cidx, lit);
    }
  }
  LOG ("Finished incsat");
  return res >= yals_card_bound (yals, cidx); // was already SAT
}

// recently flipped literal is now false with this clause
// update weighted break if necessary, udpate satcnt, update critical literal
// return true is clause is not broken/falsified
static unsigned yals_decsatcnt (Yals * yals, int cidx, int lit, int len) {
  unsigned res;
  assert_valid_cidx (cidx);
  assert_valid_len (len);
  res = yals_satcnt (yals, cidx);
  yals_setsatcnt (yals, cidx, res-1);
  res--;

  yals->ddfw.sat_count_in_clause [cidx] = res ;
#ifndef NYALSTATS
  assert (res + 1 <= yals->maxlen);
  assert (res + 1 > 0);
  assert (!yals->stats.dec[0]);
  yals->stats.dec[res + 1]++;
  assert (!yals->stats.dec[0]);
#endif

  if (yals->crit) {
    int other = yals->crit[cidx] ^ lit;
    yals->crit[cidx] = other;
    if (!yals->ddfw.ddfw_active)
    {
      if (res == 1) yals_inc_weighted_break (yals, other, len); // becomes critical
      else if (!res) yals_dec_weighted_break (yals, lit, len); // becomes falsified
    }
    assert (res || !yals->crit[cidx]);
  }
  return res;
}

/*

  Note: no ddfw weights updated here because this is called directly by
    probsat. We only update ddfw weights in the ddfw helper function that calls
    this!

  One additional literal in the cardinality constraint becomes false

  Let nsat be the number of satisfied literals before the flip, such that the
  updated number of satisfied literals is nsat - 1

  Three cases:

  1) nsat > bound + 1 : overly satisifed
    - nothing to do, already no value being added from this clause
  2) nsat = bound + 1 : becomes critical
    - sort
    - add all weights
  3) nsat <= bound  : falsified
    - remove literal from critically satisfied

  result : true if clause is not broken/falsified

*/
static unsigned yals_card_decsatcnt (Yals * yals, int cidx, int lit, int len) {
  unsigned res;
  int bound, oldnsat;
  assert_valid_card_cidx (cidx);

  res = yals_card_satcnt (yals, cidx);
  yals_card_setsatcnt (yals, cidx, res-1);
  LOGCARDCIDX (cidx, "new satcnt %d ", yals_card_satcnt (yals, cidx));
  oldnsat = res;

  yals->ddfw.card_sat_count_in_clause [cidx] = (int) res - 1;
// #ifndef NYALSTATS
//   assert (res <= yals->card_maxlen);
//   assert (res > 0);
//   assert (!yals->stats.dec[0]);
//   yals->stats.dec[res]++;
//   assert (!yals->stats.dec[0]);
// #endif

  if (yals->card_crit) {
    bound = yals_card_bound (yals, cidx);
    if (oldnsat == bound + 1)  // 2) becomes critical
        yals_card_sort_sat ( yals, cidx);
    if (!yals->ddfw.ddfw_active)
    { 
      if (oldnsat == bound + 1) { // 2) becomes critical
        yals_card_inc_all_weighted_break (yals, cidx, len); // initialize all weights
      } else if ( oldnsat <= bound ) { // 3) remove weight of flipped literal
        yals_card_dec_weighted_break (yals, lit, len);
      }
    }
    // new literal moves position
      if ( oldnsat <= (bound + 1) ) { // 3) move literal to correct spot
        yals_card_new_unsat (yals, cidx, lit);
      }
  }
  return res >= yals_card_bound (yals, cidx) + 1; // still satisfied
}




/*
  iterate over the satisfied literals of a cardinality constraint
  updating the ddfw weights

  do not update avoid_lit
*/
void yals_card_sat_weight_update (Yals *yals, int cidx, double w_diff, int avoid_lit) {
  int *begin, *end;
  assert_valid_card_cidx (cidx);
  int soft = 0;

  if ( fabs (w_diff) < 0.01 ) return; // no weight change
  LOG ("%lf", fabs (w_diff));

  if (yals->using_maxs_weights && !yals->hard_card_ids[cidx])
      soft = 1;

  yals_card_sat_iters (yals, cidx, &begin, &end);

  for (; begin != end; begin++) {
    if (*begin != avoid_lit) {
      yals_ddfw_update_var_weight (yals, *begin, soft,1, w_diff);
      LOG ("Weight added for soft? %d unsat %lf for lit %d", soft, w_diff, *begin);
    }
  }

}


/*
  iterate over the falsified literals of a cardinality constraint
  updating the ddfw weights

  do not update avoid_lit
*/
void yals_card_unsat_weight_update (Yals *yals, int cidx, double w_diff, int avoid_lit) {
  int *begin, *end;
  assert_valid_card_cidx (cidx);
  int soft = 0;

  if ( fabs (w_diff) < 0.01 ) return; // no weight change
  LOG ("%lf", fabs (w_diff));

  if (yals->using_maxs_weights && !yals->hard_card_ids[cidx])
      soft = 1;

  yals_card_unsat_iters (yals, cidx, &begin, &end);

  for (; begin != end; begin++) {
    if (*begin != avoid_lit) {
      yals_ddfw_update_var_weight (yals, *begin, soft,0, w_diff);
      LOG ("Weight added for soft? %d unsat %lf for lit %d", soft, w_diff, *begin);
    }
  }

}


/*------------------------------------------------------------------------*/

// Weight calculations

/*
  Level of abstraction for calculating normal clause ddfw weight

  Allows us to easily modify how we want to handle maxsat weights

  TODO: never used this...
*/
double yals_clause_calculate_weight (Yals * yals, int cidx) {
  // int nsat = yals_satcnt (yals, cidx);
  double ddfw_weight = yals->ddfw.ddfw_clause_weights[cidx];
  double w, clause_weight = 1.0;
  if (yals->using_maxs_weights)
    clause_weight = PEEK (yals->maxs_clause_weights, cidx);

  assert (clause_weight > 0);
  assert ( ddfw_weight > 0);

  w = ddfw_weight;
  w = w * clause_weight;
  return w;
}
 
/* 
  calculate the weight of the cardinality constraint

  c_weight is ddfw weight

  options: (1) linear weight, (2) exponential weight, (3) quadratic weight, (4) user-specified exponent

  returned weight cannot be more than WEIGHT_MAX
  
  Ideas: different weight depending on bound - nsat
    - would need something to remember the old weight, either function or array
*/
double yals_card_calculate_weight (Yals * yals, int bound, int nsat, double c_weight, int cidx) {
  double w = 0.0;
  double maxs_weight = 1.0;
  
  if (yals->using_maxs_weights && !yals->opts.maxs_init_weight_relative.val) {
    if (!yals->hard_card_ids[cidx])
      maxs_weight = PEEK (yals->maxs_card_weights, cidx);
  }

  assert (c_weight > 0);
  assert (maxs_weight > 0);

  if (yals->opts.card_compute.val == 1) {
    if (nsat < bound) {
      w =  c_weight * (bound - nsat);
    }
  } else if (yals->opts.card_compute.val == 2) { 
    if (nsat < bound) {
      if (c_weight < 1) c_weight = 1; // prevent fractions in the exponential calculation
      if ((bound - nsat) < 8) // cutoff on size of exponent
        w =  pow(c_weight,(bound - nsat));
      else 
        w = WEIGHT_MAX;
    }
   } else if (yals->opts.card_compute.val == 3) { 
    if (nsat < bound) {
      w =  c_weight * pow((bound - nsat),2);
    }
   } else if (yals->opts.card_compute.val == 4) { 
    if (nsat < bound) {
      double exp = (yals->opts.card_exp.val) / 10.0 + 1;
      w =  c_weight * pow((bound - nsat),exp);
    }
   } else {yals_abort (yals, "incorrect card_compute");}
   /*
    Possible options

    w =  c_weight * (bound - nsat) * len;

    w =  c_weight * (bound - nsat) * (len-bound);

    w =  c_weight * (bound - nsat) * const
   */
  w = MIN(w,WEIGHT_MAX);
  w = w * maxs_weight; // maxs weight multiplier
  return w;
}

// get unsat ddfw weight for a cardinality constraint
double yals_card_get_calculated_weight (Yals * yals, int cidx) {
  int bound = yals_card_bound (yals, cidx);
  int nsat = yals->ddfw.card_sat_count_in_clause[cidx];
  return yals_card_calculate_weight (yals, bound, nsat, yals->ddfw.ddfw_card_weights [cidx], cidx);
}

// get unsat ddfw weight for a cardinality constraint if an additional literal was satisfied
double yals_card_get_calculated_weight_change_pos (Yals * yals, int cidx) {
  int bound = yals_card_bound (yals, cidx);
  int nsat = yals->ddfw.card_sat_count_in_clause[cidx];
  double w = yals_card_calculate_weight (yals, bound, nsat, yals->ddfw.ddfw_card_weights [cidx], cidx);
  double w_next = yals_card_calculate_weight (yals, bound, nsat+1, yals->ddfw.ddfw_card_weights [cidx], cidx);
  assert (w - w_next >= 0);
  return w - w_next;
}

/*
  get unsat ddfw weight for a cardinality constraint if an additional literal was falsified

  used to compute the weight change for critical satisifed literals in a cardinality constraint,
  i.e., yals_card_get_calculated_weight_change_neg () - yals_card_get_calculated_weight_change_pos () 
    presents the cost if a critical literal is flipped
*/
double yals_card_get_calculated_weight_change_neg (Yals * yals, int cidx) {
  int bound = yals_card_bound (yals, cidx);
  int nsat = yals->ddfw.card_sat_count_in_clause[cidx];
  double w = yals_card_calculate_weight (yals, bound, nsat, yals->ddfw.ddfw_card_weights [cidx], cidx);
  double w_next = yals_card_calculate_weight (yals, bound, nsat-1, yals->ddfw.ddfw_card_weights [cidx], cidx);
  
  if (nsat == 0) {
    return 0.0;
  }
  // yals_msg (yals, 1, "old %lf, new %lf",w, w_next);
  assert (w_next - w > -0.01); // next weight is the same or larger
  return w_next - w;
}




/*------------------------------------------------------------------------*/

// helper functions for reporting solutions

static void yals_report (Yals * yals, const char * fmt, ...) {
  double t, f;
  va_list ap;
  assert (yals->opts.verbose.val);
  yals_msglock (yals);
  f = yals->stats.flips;
  t = yals_sec (yals);
  fprintf (yals->out, "%s", yals->opts.prefix);
  va_start (ap, fmt);
  vfprintf (yals->out, fmt, ap);
  va_end (ap);
  fprintf (yals->out,
    " : best %d (tmp %d), clauses %d, constraints %d, flips %.0f, %.2f sec, %.2f kflips/sec\n",
    yals->stats.best, yals->stats.tmp,yals->stats.best_clauses, yals->stats.best_cardinality, f, t, yals_avg (f/1e3, t));
  fflush (yals->out);
  yals_msgunlock (yals);
}

int yals_clauses_nunsat (Yals * yals) { 

  yals_msg (yals, 4, "falsified clause cnt %d", COUNT (yals->unsat.stack));

  if (yals->unsat.usequeue) return yals->unsat.queue.count;
  else return COUNT (yals->unsat.stack);
}

int yals_card_nunsat (Yals * yals) { 
  assert (!yals->unsat.usequeue); // only using the stack...

  yals_msg (yals, 4, "falsified card cnt %d", COUNT (yals->card_unsat.stack));

  if (yals->unsat.usequeue) return yals->card_unsat.queue.count;
  else return COUNT (yals->card_unsat.stack);
}

double yals_clause_weight_unsat (Yals * yals) { 
  return (yals->unsat_soft.maxs_weight);
}

double yals_card_weight_unsat (Yals * yals) { 
  assert (!yals->unsat.usequeue); // only using the stack...

  return (yals->card_unsat_soft.maxs_weight);
}

int yals_clause_hard_unsat (Yals * yals) { 
  return yals_clauses_nunsat (yals);
}

int yals_card_hard_unsat (Yals * yals) { 
  assert (!yals->unsat.usequeue); // only using the stack...

  return yals_card_nunsat (yals);
}

int yals_hard_unsat (Yals * yals) {
  return yals_clause_hard_unsat (yals) + yals_card_hard_unsat (yals);
}

int yals_clause_soft_unsat (Yals * yals) { 
  return COUNT (yals->unsat_soft.stack);
}

int yals_card_soft_unsat (Yals * yals) { 
  assert (!yals->unsat.usequeue); // only using the stack...

  return COUNT (yals->card_unsat_soft.stack);
}

int yals_soft_unsat (Yals * yals) {
  return yals_clause_soft_unsat (yals) + yals_card_soft_unsat (yals);
}

// double yals_cost_unsat (Yals * yals) { // now grabbing from all types of clauses
//   return yals_clause_weight_unsat (yals) + yals_card_weight_unsat (yals);
// }

int yals_nunsat (Yals * yals) { // now grabbing from all types of clauses
  return yals_clauses_nunsat (yals) + yals_card_nunsat (yals);
}

// save new minimum cost assignment
// update statistics
void yals_save_new_minimum (Yals * yals) {
  int nunsat = yals_nunsat (yals);
  yals_msg (yals, 4, "nunsat %d", nunsat);
  size_t bytes = yals->nvarwords * sizeof (Word);
  if (yals->stats.worst < nunsat) yals->stats.worst = nunsat;
  if (yals->stats.tmp > nunsat) {
    LOG ("minimum %d is best assignment since last restart", nunsat);
    memcpy (yals->tmp, yals->vals, bytes);
    yals->stats.tmp = nunsat;
  }
  if (yals->stats.best < nunsat) return;
  if (yals->stats.best == nunsat) {
    LOG ("minimum %d matches previous overall best assignment", nunsat);
    yals->stats.hits++;
    return;
  }
  LOG ("minimum %d with new best overall assignment", nunsat);
  yals->stats.best = nunsat;
  yals->stats.best_clauses = yals_clauses_nunsat (yals);
  yals->stats.best_cardinality = yals_card_nunsat (yals);
  yals->stats.hits = 1;
  memcpy (yals->best, yals->vals, bytes);
  if (yals->opts.verbose.val >= 2 ||
      (yals->opts.verbose.val >= 1 && nunsat <= yals->limits.report.min/2)) {
    yals_report (yals, "new minimum");
    yals->limits.report.min = nunsat;
  }

}

/*------------------------------------------------------------------------*/

static int yals_pick_by_score (Yals * yals) {
  double s, lim, sum;
  const double * q;
  const int * p;
  int res;

  assert (!EMPTY (yals->scores));
  assert (COUNT (yals->scores) == COUNT (yals->cands));

  sum = 0;
  for (q = yals->scores.start; q < yals->scores.top; q++)
    sum += *q;

  assert (sum > 0);
  lim = (yals_rand (yals) / (1.0 + (double) UINT_MAX))*sum;
  assert (lim < sum);

  LOG ("random choice %g mod %g", lim, sum);

  p = yals->cands.start; assert (p < yals->cands.top);
  res = *p++;

  q = yals->scores.start; assert (q < yals->scores.top);
  s = *q++; assert (s > 0);

  while (p < yals->cands.top && s <= lim) {
    lim -= s;
    res = *p++; assert (q < yals->scores.top);
    s = *q++; assert (s > 0);
  }

  return res;
}

/*------------------------------------------------------------------------*/

void yals_flip_value_of_lit (Yals * yals, int lit) {
  int idx = ABS (lit);
  LOG ("flipping %d", lit);
  NOTBIT (yals->vals, yals->nvarwords, idx);
  yals->flips[idx]++;
}


/*------------------------------------------------------------------------*/
/* --litheap: per-literal max-weight neighbor heaps (option A).             */
/*                                                                          */
/* For each literal we keep one max-heap over the constraints (clauses AND  */
/* cardinality constraints, mixed) that contain it, keyed by the current    */
/* DDFW weight. yals_ddfw_get_max_weight_sat_clause can then peek each       */
/* falsified literal's heaviest neighbor instead of scanning all of its     */
/* occurrences. Heaps are maintained only on weight changes (transfers);    */
/* satisfaction is a dynamic, weight-uncorrelated predicate, so it is       */
/* checked lazily at query time (the top may be unsatisfied).               */
/*                                                                          */
/* Encoding: a "unified" constraint id u is a clause cidx if u < nclauses,  */
/* else cardinality cidx (u - nclauses). Each (constraint, literal) pair is  */
/* an "edge"; edges are numbered constraint-major (so a constraint's edges  */
/* are contiguous) and partitioned into per-literal heaps held in nbr_heap. */
/*------------------------------------------------------------------------*/

static inline double yals_nbr_weight (Yals * yals, int u) {
  return (u < yals->nclauses)
    ? yals->ddfw.ddfw_clause_weights [u]
    : yals->ddfw.ddfw_card_weights [u - yals->nclauses];
}

// Ranking used throughout: a constraint ranks above another if it has greater
// DDFW weight, with ties broken by smaller unified constraint id. This is a
// total order (no ties), so the scan and the heap always select the same
// source -- the search path is identical with and without --litheap.
// e1, e2 are edge ids.
static inline int yals_nbr_better (Yals * yals, int e1, int e2) {
  int u1 = yals->ddfw.nbr_con[e1], u2 = yals->ddfw.nbr_con[e2];
  double w1 = yals_nbr_weight (yals, u1), w2 = yals_nbr_weight (yals, u2);
  if (w1 != w2) return w1 > w2;
  return u1 < u2;
}

static void yals_nbr_siftup (Yals * yals, int g) {
  int * heap = yals->ddfw.nbr_heap, * gpos = yals->ddfw.nbr_gpos;
  int e = heap[g], lo = yals->ddfw.nbr_lstart[yals->ddfw.nbr_lit[e]];
  while (g > lo) {
    int par = lo + (g - lo - 1) / 2, pe = heap[par];
    if (!yals_nbr_better (yals, e, pe)) break;
    heap[g] = pe; gpos[pe] = g; g = par;
  }
  heap[g] = e; gpos[e] = g;
}

static void yals_nbr_siftdown (Yals * yals, int g) {
  int * heap = yals->ddfw.nbr_heap, * gpos = yals->ddfw.nbr_gpos;
  int e = heap[g], p = yals->ddfw.nbr_lit[e];
  int lo = yals->ddfw.nbr_lstart[p], hi = yals->ddfw.nbr_lstart[p+1];
  for (;;) {
    int l = lo + 2*(g - lo) + 1, r = l + 1, bestslot = -1, beste = e;
    if (l < hi && yals_nbr_better (yals, heap[l], beste)) { beste = heap[l]; bestslot = l; }
    if (r < hi && yals_nbr_better (yals, heap[r], beste)) { beste = heap[r]; bestslot = r; }
    if (bestslot < 0) break;
    heap[g] = beste; gpos[beste] = g; g = bestslot;
  }
  heap[g] = e; gpos[e] = g;
}

// A single constraint's weight changed: re-sift each of its edges.
static void yals_nbr_update (Yals * yals, int u) {
  if (!yals->ddfw.nbr_built) return;
  for (int e = yals->ddfw.nbr_cstart[u]; e < yals->ddfw.nbr_cstart[u+1]; e++) {
    yals_nbr_siftup (yals, yals->ddfw.nbr_gpos[e]);
    yals_nbr_siftdown (yals, yals->ddfw.nbr_gpos[e]);
  }
}

// Best (max-weight) *eligible* neighbor of lit: satisfied and >= initial
// weight. Returns the per-type cidx and sets *ret_con_type, or -1 if none.
// Explores the max-heap in decreasing-weight order (no mutation), so the
// first eligible node found is the maximum-weight eligible one.
static int yals_nbr_best (Yals * yals, int lit, int * ret_con_type) {
  int p = get_pos (lit);
  int lo = yals->ddfw.nbr_lstart[p], hi = yals->ddfw.nbr_lstart[p+1];
  if (hi <= lo) return -1;
  int relative = (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights);
  int * heap = yals->ddfw.nbr_heap, * con = yals->ddfw.nbr_con;
  int * fr = yals->ddfw.nbr_scratch, frn = 0;
  fr[frn++] = lo;
  while (frn > 0) {
    int bi = 0;
    for (int i = 1; i < frn; i++)
      if (yals_nbr_better (yals, heap[fr[i]], heap[fr[bi]])) bi = i;
    int s = fr[bi]; fr[bi] = fr[--frn];
    int u = con[heap[s]];
    if (u < yals->nclauses) {
      double thr = (relative && !yals->hard_clause_ids[u])
                   ? PEEK (yals->maxs_clause_weights, u)
                   : (double) yals->opts.init_clause_weight.val;
      if (yals_satcnt (yals, u) > 0 &&
          (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_clause_weights[u] >= thr)) {
        *ret_con_type = TYPECLAUSE; return u;
      }
    } else {
      int c = u - yals->nclauses;
      double thr = (relative && !yals->hard_card_ids[c])
                   ? PEEK (yals->maxs_card_weights, c)
                   : (double) yals->opts.init_card_weight.val;
      if (yals_card_satcnt (yals, c) >= yals_card_bound (yals, c) &&
          (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_card_weights[c] >= thr)) {
        *ret_con_type = TYPECARDINALITY; return c;
      }
    }
    int li = lo + 2*(s - lo) + 1, ri = li + 1;
    if (li < hi) fr[frn++] = li;
    if (ri < hi) fr[frn++] = ri;
  }
  return -1;
}

// Re-establish heap order for every per-literal partition (used after a
// bulk weight change, e.g. reset_weights_on_restart). Membership unchanged.
static void yals_nbr_reheapify (Yals * yals) {
  if (!yals->ddfw.nbr_built) return;
  for (int p = 0; p < yals->ddfw.nbr_nlits; p++) {
    int lo = yals->ddfw.nbr_lstart[p], hi = yals->ddfw.nbr_lstart[p+1], n = hi - lo;
    for (int i = n/2 - 1; i >= 0; i--) yals_nbr_siftdown (yals, lo + i);
  }
}

static void yals_nbr_free (Yals * yals) {
  if (!yals->ddfw.nbr_built) return;
  free (yals->ddfw.nbr_con);   free (yals->ddfw.nbr_lit);
  free (yals->ddfw.nbr_gpos);  free (yals->ddfw.nbr_heap);
  free (yals->ddfw.nbr_cstart); free (yals->ddfw.nbr_lstart);
  free (yals->ddfw.nbr_scratch);
  yals->ddfw.nbr_built = 0;
}

static void yals_nbr_build (Yals * yals) {
  int ncl = yals->nclauses, ncard = yals->card_nclauses;
  int ncons = ncl + ncard, nlits = 2 * yals->nvars;
  int * cstart = malloc ((ncons + 1) * sizeof (int));
  int * lstart = calloc (nlits + 1, sizeof (int));
  int E = 0;
  const int * pl;
  for (int u = 0; u < ncl; u++) {
    cstart[u] = E;
    for (pl = yals_lits (yals, u); *pl; pl++) { E++; lstart[get_pos (*pl) + 1]++; }
  }
  for (int u = 0; u < ncard; u++) {
    cstart[ncl + u] = E;
    int len = yals_card_length (yals, u);
    pl = yals_card_lits (yals, u);
    for (int j = 0; j < len; j++) { E++; lstart[get_pos (pl[j]) + 1]++; }
  }
  cstart[ncons] = E;
  for (int i = 0; i < nlits; i++) lstart[i+1] += lstart[i];

  int * con = malloc (E * sizeof (int)), * litp = malloc (E * sizeof (int));
  int * gpos = malloc (E * sizeof (int)), * heap = malloc (E * sizeof (int));
  int * fill = malloc (nlits * sizeof (int));
  for (int i = 0; i < nlits; i++) fill[i] = lstart[i];
  int e = 0, maxocc = 1;
  for (int u = 0; u < ncl; u++)
    for (pl = yals_lits (yals, u); *pl; pl++) {
      int pp = get_pos (*pl); con[e] = u; litp[e] = pp;
      int g = fill[pp]++; heap[g] = e; gpos[e] = g; e++;
    }
  for (int u = 0; u < ncard; u++) {
    int len = yals_card_length (yals, u);
    pl = yals_card_lits (yals, u);
    for (int j = 0; j < len; j++) {
      int pp = get_pos (pl[j]); con[e] = ncl + u; litp[e] = pp;
      int g = fill[pp]++; heap[g] = e; gpos[e] = g; e++;
    }
  }
  free (fill);
  for (int i = 0; i < nlits; i++) { int c = lstart[i+1] - lstart[i]; if (c > maxocc) maxocc = c; }

  yals->ddfw.nbr_con = con; yals->ddfw.nbr_lit = litp;
  yals->ddfw.nbr_gpos = gpos; yals->ddfw.nbr_heap = heap;
  yals->ddfw.nbr_cstart = cstart; yals->ddfw.nbr_lstart = lstart;
  yals->ddfw.nbr_E = E; yals->ddfw.nbr_ncons = ncons; yals->ddfw.nbr_nlits = nlits;
  yals->ddfw.nbr_scratch = malloc ((maxocc + 2) * sizeof (int));
  yals->ddfw.nbr_built = 1;
  yals_nbr_reheapify (yals);
}

// reset stacks, ddfw weight change values, ddfw constraint weights (if option is set)
void yals_reset_ddfw (Yals * yals)
{
  CLEAR (yals->ddfw.uvars);
  for (int v=1; v<yals->nvars; v++)
  {
    yals->ddfw.var_unsat_count [v] = 0;
    yals->ddfw.uvar_pos [v] = -1;
    yals->ddfw.uvar_changed_pos [v] = -1;
  }

  for (int i=1; i< yals->nvars; i++)
  {
    yals->ddfw.unsat_weights [get_pos (i)] = 0;
    yals->ddfw.unsat_weights [get_pos (-i)] =0;
    yals->ddfw.sat1_weights [get_pos (i)] = 0;
    yals->ddfw.sat1_weights [get_pos (-i)] = 0;
  }

  yals_clear_heap (yals, &yals->ddfw.uvars_heap);
  if (yals->using_maxs_weights) {
    yals_clear_heap (yals, &yals->ddfw.uvars_heap_soft);
    CLEAR (yals->ddfw.uvars_soft);
    for (int v=1; v<yals->nvars; v++)
    {
      yals->ddfw.var_unsat_count_soft [v] = 0;
      yals->ddfw.uvar_pos_soft [v] = -1;
    }

    for (int i=1; i< yals->nvars; i++)
    {
      yals->ddfw.unsat_weights_soft [get_pos (i)] = 0;
      yals->ddfw.unsat_weights_soft [get_pos (-i)] =0;
      yals->ddfw.sat1_weights_soft [get_pos (i)] = 0;
      yals->ddfw.sat1_weights_soft [get_pos (-i)] = 0;
    }
  }

  // for resetting constraint weights on restart
  if (yals->opts.reset_weights_on_restart.val) {
    for (int i=0; i< yals->nclauses; i++) {
      if (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights && !yals->hard_clause_ids[i])
        yals->ddfw.ddfw_clause_weights [i] = PEEK (yals->maxs_clause_weights, i);
      else
        yals->ddfw.ddfw_clause_weights [i] = yals->opts.init_clause_weight.val;
    }
    for (int i=0; i< yals->card_nclauses; i++) {
      if (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights && !yals->hard_card_ids[i])
        yals->ddfw.ddfw_card_weights [i] = PEEK (yals->maxs_card_weights, i);
      else
        yals->ddfw.ddfw_card_weights [i] = yals->opts.init_card_weight.val;
    }
    // --litheap: weights changed in bulk; restore heap order.
    if (yals->opts.litheap.val) yals_nbr_reheapify (yals);
  }
}

static void yals_reset_unsat (Yals * yals) {
  assert (!yals->unsat.usequeue);
  if (yals->unsat.usequeue) yals_reset_unsat_queue (yals); // queue is not supported
  else yals_reset_unsat_stack (yals);
}


/*------------------------------------------------------------------------*/

void yals_make_clauses_after_flipping_lit (Yals * yals, int lit) {
  double start = yals_time (yals);
  const int * p, * occs;
  int cidx, len, occ;
  double card_unsat_weight_change, card_new_unsat_weight, card_old_critical_weight, \
  card_new_critical_weight, card_critical_weight_change, card_old_unsat_weight;
  int bound, oldnsat;
  int soft = 0;
  double maxs_weight = 1.0;
#if !defined(NDEBUG) || !defined(NYALSTATS)
  int made = 0;
#endif
  assert (yals_val (yals, lit));
  occs = yals_occs (yals, lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    len = occ & LENMASK;
    cidx = occ >> LENSHIFT;
    maxs_weight = 1.0;
    if (yals_incsatcnt (yals, cidx, lit, len))
    {  // clause was already sat
      if (yals->ddfw.sat_count_in_clause [cidx] == 2) // 1 to 2
      {  // updating sat weights when moving from 1 to 2, becasue it is no longer critical

        soft = 0;
        if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
          soft = 1;
          if (!yals->opts.maxs_init_weight_relative.val)
            maxs_weight = PEEK (yals->maxs_clause_weights, cidx);
        }

        int other = yals->crit [cidx] ^ lit; // ignore the second lit that was just xor'd onto crit    
        // sat1_weights [get_pos(other)] -= yals->ddfw.ddfw_clause_weights [cidx];
        yals_ddfw_update_var_weight (yals, other, soft,1, -yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
      }
      continue;
    }
    // else unsat clause now made
    yals_ddfw_update_lit_weights_on_make (yals, cidx, lit);

    // yals_remove_a_var_from_uvars (yals, lit, soft);

    yals_dequeue (yals, cidx,TYPECLAUSE);
    LOGCIDX (cidx, "made");
#if !defined(NDEBUG) || !defined(NYALSTATS)
    made++;
#endif
    
  }
  LOG ("flipping %d has made %d clauses", lit, made);
#ifndef NYALSMEMS
  {
    int updated = p - occs;
    ADD (update, updated);
    if (yals->crit) ADD (crit, updated);
  }
#endif
#ifndef NYALSTATS
  yals->stats.made += made;
#endif

  // make cardinality constraints
/*

  One additional literal in the cardinality constraint becomes satisified

  Let nsat be the number of satisfied literals before the flip, such that the
  updated number of satisfied literals is nsat +1

  That literal was sorted correctly in call to incsatcnt (if needed to be sorted)

  Four cases:

  1) oldnsat > bound : overly satisifed
    - nothing to do, already no value being added from this clause
  2) oldnsat = bound : overly satisfied and no longer critical
    - remove critical weights from the break weight
    - not new lit!
  3) oldnsat = bound-1 : becomes critically satisfied
    - add lit to sat1 weights
    - remove all unsat weights
    - remove lit from unsat weights
    - update sat1 weights
  4) nsat < bound -1 : falsified still
    - add new lit to the critical weights as a break lit
    - remove lit from unsat weight
    - update sat1 weights
    - update unsat weights
  
*/

#if !defined(NDEBUG) || !defined(NYALSTATS)
  made = 0;
#endif
  assert (yals_val (yals, lit));
  occs = yals_card_occs (yals, lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    len = occ & LENMASK;
    cidx = occ >> LENSHIFT;

    bound = yals_card_bound (yals, cidx);
    oldnsat = yals_card_satcnt (yals, cidx);

    // get all old/new/changed ddfw weights necessary for update
    card_old_unsat_weight = yals_card_get_calculated_weight (yals, cidx);
    card_old_critical_weight = yals_card_get_calculated_weight_change_neg (yals, cidx);

    // increment satcnt of cardinality constraint, move lit to correct partition
    yals_card_incsatcnt (yals, cidx, lit, len);
    
    card_new_unsat_weight = yals_card_get_calculated_weight (yals, cidx);
    card_unsat_weight_change =  card_new_unsat_weight - card_old_unsat_weight;
    // card_new_critical_weight = -1.0 * card_unsat_weight_change; // caused error for some reason (off by 4/3)
    card_new_critical_weight = yals_card_get_calculated_weight_change_neg (yals, cidx);

    card_critical_weight_change = card_new_critical_weight - card_old_critical_weight;

    assert (card_unsat_weight_change <= 0); // weight must get smaller or stay the same

    // Debugging information
    // if (oldnsat <= bound) {
    //   LOG ("PRELOG");
    //   LOGCARDCIDX (cidx, "old nsat %d new nsat %d bound %d",oldnsat,  yals_card_satcnt (yals, cidx), bound);
    //   LOG ("old unsat %lf new unsat %lf unsat change %lf old crit %lf new crit %lf",\
    //   card_old_unsat_weight, card_new_unsat_weight, card_unsat_weight_change, card_old_critical_weight, card_new_critical_weight );
    // }
    
    soft = 0;
    if (yals->using_maxs_weights && !yals->hard_card_ids[cidx])
      soft = 1;

    if (oldnsat > bound) { // 1)
      continue;
    } else if (oldnsat == bound) { // 2)
      // remove critical weights
      yals_card_sat_weight_update (yals, cidx, -card_old_critical_weight, lit);
    } else if (oldnsat == bound - 1) { // 3)
      // remove unsat weights
      yals_card_unsat_weight_update (yals, cidx, -card_old_unsat_weight, lit);
      // remove unsat weight of lit
      // unsat_weights[get_pos (lit)] -= card_old_unsat_weight;
      yals_ddfw_update_var_weight (yals, lit, soft,0, -card_old_unsat_weight);

      // change critical weights
      yals_card_sat_weight_update (yals, cidx, card_critical_weight_change, lit);

      // add critical weight of lit
      // sat1_weights[get_pos (lit)] += card_new_critical_weight;
      yals_ddfw_update_var_weight (yals, lit, soft,1,card_new_critical_weight);

      // yals_remove_a_var_from_uvars (yals, lit, soft);

      yals_dequeue (yals, cidx,TYPECARDINALITY);
    LOGCARDCIDX (cidx, "made");
#if !defined(NDEBUG) || !defined(NYALSTATS)
    made++;
#endif

    } else if (oldnsat < bound - 1) { // 4)
      // remove unsat weight of lit
      // unsat_weights[get_pos (lit)] -= card_old_unsat_weight;
      yals_ddfw_update_var_weight (yals, lit, soft,0,-card_old_unsat_weight);

      // add critical weight of lit
      // sat1_weights[get_pos (lit)] += card_new_critical_weight;
      yals_ddfw_update_var_weight (yals, lit, soft,1,card_new_critical_weight);

      // change critical weights of lits
      yals_card_sat_weight_update (yals, cidx, card_critical_weight_change, lit);

      // change unsat weights of lits
      yals_card_unsat_weight_update (yals, cidx, card_unsat_weight_change, lit);

      // yals_remove_a_var_from_uvars (yals, lit, soft);
    }
    // yals->ddfw.card_clause_calculated_weights[cidx] = card_new_unsat_weight;
  }
  LOG ("flipping %d has made %d cardinality constraints", lit, made);
#ifndef NYALSMEMS
  {
    int updated = p - occs;
    ADD (update, updated);
    if (yals->crit) ADD (crit, updated);
  }
#endif
#ifndef NYALSTATS
  yals->stats.made += made;
#endif

  yals->stats.maxs_time.make_time += yals_time (yals) - start;
}

void yals_break_clauses_after_flipping_lit (Yals * yals, int lit) {
  double start = yals_time (yals);
  const int * p, * occs;
  int occ, cidx, len;
  double card_unsat_weight_change, card_new_unsat_weight, card_old_critical_weight, \
  card_new_critical_weight, card_critical_weight_change, card_old_unsat_weight;
  int bound, oldnsat;
  int soft = 0;
  double maxs_weight = 1.0;
#if !defined(NDEBUG) || !defined(NYALSTATS)
  int broken = 0;
#endif
  occs = yals_occs (yals, -lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    len = occ & LENMASK;
    cidx = occ >> LENSHIFT;
    maxs_weight = 1.0;
    if (yals_decsatcnt (yals, cidx, -lit, len))
    { // clause still sat
       if (yals->ddfw.sat_count_in_clause [cidx] == 1) { // 2 to 1

        soft = 0;
        if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
          soft = 1;
          if (!yals->opts.maxs_init_weight_relative.val)
            maxs_weight = PEEK (yals->maxs_clause_weights, cidx);
        }

        // sat1_weights [get_pos(yals->crit[cidx])] += yals->ddfw.ddfw_clause_weights [cidx];
        yals_ddfw_update_var_weight (yals, yals->crit[cidx], soft,1, yals->ddfw.ddfw_clause_weights [cidx]);
       }
      continue;
    }
    // else clause now unsat (broken)
    yals_ddfw_update_lit_weights_on_break (yals, cidx, lit);
    yals_enqueue (yals, cidx, TYPECLAUSE);
    LOGCIDX (cidx, "broken");
#if !defined(NDEBUG) || !defined(NYALSTATS)
    broken++;
#endif
  }
  LOG ("flipping %d has broken %d clauses", lit, broken);
#ifndef NYALSMEMS
  {
    int updated = p - occs;
    ADD (update, updated);
    if (yals->crit) ADD (crit, updated);
  }
#endif
#ifndef NYALSTATS
  yals->stats.broken += broken;
#endif

// break cardinality constraints
/*

  One additional literal in the cardinality constraint becomes falsified

  That literal was sorted correctly in call to decsatcnt (if needed to be sorted)

  Four cases:

  1) oldnsat > bound + 1 : overly satisifed
    - nothing to do, already no value being added from this clause
  2) oldnsat = bound + 1 : critically sat
    - add all sat1 weights
  3) oldnsat = bound : becomes falsified
    - add all unsat weights
    - update critical weights
    - lit removed from critical weights
  4) nsat < bound : falsified still
    - add lit to unsat
    - remove lit from critical
    - update all criticals
    - update all unsats
  
*/

#if !defined(NDEBUG) || !defined(NYALSTATS)
  broken = 0;
#endif
  occs = yals_card_occs (yals, -lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    len = occ & LENMASK;
    cidx = occ >> LENSHIFT;

    bound = yals_card_bound (yals, cidx);
    oldnsat = yals_card_satcnt (yals, cidx);

    // get all old/new/changed ddfw weights necessary for update
    card_old_unsat_weight = yals_card_get_calculated_weight (yals, cidx);
    card_old_critical_weight = yals_card_get_calculated_weight_change_neg (yals, cidx);

    // decrement satcnt of cardinality constraint, move lit to correct partition
    yals_card_decsatcnt (yals, cidx,-lit, len);
    
    card_new_unsat_weight = yals_card_get_calculated_weight (yals, cidx);
    card_unsat_weight_change =  card_new_unsat_weight - card_old_unsat_weight;
    // card_old_critical_weight = card_unsat_weight_change; // caused error for some reason
    card_new_critical_weight = yals_card_get_calculated_weight_change_neg (yals, cidx);

    card_critical_weight_change = card_new_critical_weight - card_old_critical_weight;

    // Debugging information
    // if (oldnsat <= bound+1) {
    //   LOGCARDCIDX (cidx, "old nsat %d new nsat %d bound %d",oldnsat,  yals_card_satcnt (yals, cidx), bound);
    //   LOG ("old unsat %lf new unsat %lf unsat change %lf old crit %lf new crit %lf",\
    //   card_old_unsat_weight, card_new_unsat_weight, card_unsat_weight_change, card_old_critical_weight, card_new_critical_weight );
    // }

    soft = 0;
    if (yals->using_maxs_weights && !yals->hard_card_ids[cidx])
      soft = 1;

    if (oldnsat > bound+1) { // 1)
      continue;
    } else if (oldnsat == bound+1) { // 2)
      // add critical weights
      yals_card_sat_weight_update (yals, cidx, card_new_critical_weight, -lit);
    } else if (oldnsat == bound) { // 3)
      // remove unsat weights
      yals_card_unsat_weight_update (yals, cidx, card_new_unsat_weight, 0);
      
      // remove critical weight of lit
      // sat1_weights[get_pos (-lit)] -= card_old_critical_weight;
      yals_ddfw_update_var_weight (yals,-lit, soft, 1, -card_old_critical_weight);

      // change critical weights
      yals_card_sat_weight_update (yals, cidx, card_critical_weight_change, -lit);

      yals_enqueue (yals, cidx,TYPECARDINALITY);
    LOGCARDCIDX (cidx, "broken");
#if !defined(NDEBUG) || !defined(NYALSTATS)
    broken++;
#endif

    } else if (oldnsat < bound ) { // 4)
      assert (card_unsat_weight_change >= 0); // weight must get larger or stay the same

      // remove critical weight of lit
      // sat1_weights[get_pos (-lit)] -= card_old_critical_weight;
      yals_ddfw_update_var_weight (yals,-lit, soft, 1, -card_old_critical_weight);

      // add unsat weight of lit
      // unsat_weights[get_pos (-lit)] += card_new_unsat_weight;
      yals_ddfw_update_var_weight (yals,-lit, soft, 0, card_new_unsat_weight);

      // change critical weights of lits
      yals_card_sat_weight_update (yals, cidx, card_critical_weight_change, -lit);

      // change unsat weights of lits
      yals_card_unsat_weight_update (yals, cidx, card_unsat_weight_change, -lit);

      // when flipped lit in constraint already broken, should be added to uvars (not enqueued though)
      yals_add_a_var_to_uvars (yals, lit, soft);
    }
    // yals->ddfw.card_clause_calculated_weights[cidx] = card_new_unsat_weight;
  }
  LOG ("flipping %d has broken %d cardinality constraints", lit, broken);
#ifndef NYALSMEMS
  {
    int updated = p - occs;
    ADD (update, updated);
    if (yals->crit) ADD (crit, updated);
  }
#endif
#ifndef NYALSTATS
  yals->stats.broken += broken;
#endif

  yals->stats.maxs_time.break_time += yals_time (yals) - start;
}

static void yals_update_minimum (Yals * yals) {
  yals_save_new_minimum (yals);
  LOG ("now %d hard clauses unsatisfied", yals_nunsat (yals));
  yals_check_global_satisfaction_invariant (yals);
}

void yals_flip_ddfw (Yals * yals, int lit) {
  //yals_check_lits_weights_sanity (yals); // checking in weight invariant now
  yals->stats.flips++;
  yals->stats.unsum += yals_nunsat (yals);
  yals->ddfw.last_flipped = lit;

  // Debugging information
  //printf ("\n P =====> %d %d",yals->stats.flips, lit);
//   if (yals->stats.flips % 100000 == 0)
//    {
//     printf ("\n P ====> %d %d %d %d %d %d %.40f", 
//        yals->stats.flips, lit, yals->ddfw.uwrvs_size, 
//        yals->ddfw.local_minima, yals_nunsat (yals), yals->ddfw.uwrvs [yals->ddfw.uwrvs_size-1],  yals->ddfw.uwvars_gains [yals->ddfw.uwrvs_size-1]);
// //   //printf ("\n flip_time/uwrv/candidate ====> %f/%f/%f",yals->ddfw.flip_time,yals->ddfw.uwrv_time, yals->ddfw.compute_uwvars_from_unsat_clauses_time);
//   //printf ("\n WT/neighborhood/candidate ====> %f/%f/%f",yals->ddfw.wtransfer_time, yals->ddfw.neighborhood_comp_time, yals->ddfw.compute_uwvars_from_unsat_clauses_time);

//   }
  //

  yals_msg (yals, 3, "flipping %d\n",lit);

  yals_flip_value_of_lit (yals, lit);

  LOG ("reset positions after flip %d", lit);
  int var = ABS (lit);
  // remove from uvar stack
  if (yals->ddfw.uvar_pos [var] > -1) {
    yals->ddfw.var_unsat_count [var] = 0;
    int remove_pos = yals->ddfw.uvar_pos [var];
    int top_element = TOP (yals->ddfw.uvars);
    POKE (yals->ddfw.uvars, remove_pos, top_element);
    yals->ddfw.uvar_pos [top_element] = remove_pos;
    POP (yals->ddfw.uvars);
    yals->ddfw.uvar_pos [var] = -1;
  }

  // remove from uvar soft stack
  if (yals->using_maxs_weights) {
    if (yals->ddfw.uvar_pos_soft [var] > -1) {
      yals->ddfw.var_unsat_count_soft [var] = 0;
      int remove_pos = yals->ddfw.uvar_pos_soft [var];
      int top_element = TOP (yals->ddfw.uvars_soft);
      POKE (yals->ddfw.uvars_soft, remove_pos, top_element);
      yals->ddfw.uvar_pos_soft [top_element] = remove_pos;
      POP (yals->ddfw.uvars_soft);
      yals->ddfw.uvar_pos_soft [var] = -1;
    }
  }

  LOG ("update constraints after flip %d", lit);

  yals_make_clauses_after_flipping_lit (yals, -lit);
  yals_break_clauses_after_flipping_lit (yals, -lit);
  if (!yals->using_maxs_weights) // otherwise cost saved separately
    yals_update_minimum (yals);
  yals->last_flip_unsat_count = yals_nunsat (yals);
}

/*------------------------------------------------------------------------*/

static Word yals_primes[] = {
  2000000011u, 2000000033u, 2000000063u, 2000000087u, 2000000089u,
  2000000099u, 2000000137u, 2000000141u, 2000000143u, 2000000153u,
  2000000203u, 2000000227u, 2000000239u, 2000000243u, 2000000269u,
  2000000273u, 2000000279u, 2000000293u, 2000000323u, 2000000333u,
  2000000357u, 2000000381u, 2000000393u, 2000000407u, 2000000413u,
  2000000441u, 2000000503u, 2000000507u, 2000000531u, 2000000533u,
  2000000579u, 2000000603u, 2000000609u, 2000000621u, 2000000641u,
  2000000659u, 2000000671u, 2000000693u, 2000000707u, 2000000731u,
};

#define NPRIMES (sizeof(yals_primes)/sizeof(unsigned))

static Word yals_sig (Yals * yals) {
  unsigned i = 0, j;
  Word res = 0;
  for (j = 0; j < yals->nvarwords; j++) {
    res += yals_primes[i++] * yals->vals[j];
    if (i == NPRIMES) i = 0;
  }
  return res;
}

static unsigned yals_gcd (unsigned a, unsigned b) {
  while (b) {
    unsigned r = a % b;
    a = b, b = r;
  }
  return a;
}

/*------------------------------------------------------------------------*/
/* Shared assignment cache for parallel (palsat) workers.                 */
/*                                                                        */
/* Workers share a fixed-capacity pool of "good" assignments. Each time a */
/* worker reaches its restart boundary (cutoff hit on the previous try),  */
/* it (1) releases the cache slot it had been working on, (2) inserts its */
/* best-of-try assignment, and (3) picks a new starting assignment by     */
/* weighted random selection over unreserved slots (better cost -> higher */
/* weight). The picked slot is reserved by this worker so no other worker */
/* starts from the same assignment concurrently.                          */
/*                                                                        */
/* All policy choices are runtime-configurable via YalsSharedCacheConfig. */
/*------------------------------------------------------------------------*/

struct YalsSharedCache {
  pthread_mutex_t lock;
  YalsSharedCacheConfig cfg;
  int count;                  // number of allocated slots
  int nvars;                  // set on first insert
  int nvarwords;              // set on first insert
  int hamming_threshold;      // computed = max(1, percent*nvars/100)
  int nworkers;
  Word ** vals;               // [capacity] each NULL until allocated
  int *   mins;               // [capacity] cost (yals_minimum) per slot
  int *   reserved;           // [capacity] owner worker id or -1
  int *   worker_slot;        // [nworkers] slot each worker reserves or -1
  int *   worker_restarts;    // [nworkers] count of restarts seen so far
  int *   worker_start_cost;  // [nworkers] cost at start-of-current-try (INT_MAX if none)
  long long * pick_count;     // [capacity] times each slot has been picked (reset on replace)
  // stats
  long long s_inserted, s_replaced_ham, s_replaced_worse;
  long long s_skipped_close_worse, s_skipped_no_room, s_skipped_empty;
  long long s_skipped_no_improve;
  long long s_picked, s_pick_empty, s_pick_warmup, s_pick_explore;
};

void yals_shared_cache_config_init (YalsSharedCacheConfig * cfg) {
  // Defaults tuned across multiple ntil instance sizes (30..43, sweep5:
  // 4 hard instances x 5 seeds x 300s budget). The configuration
  // `pick=UNIFORM, explore=0` was first or top-5 on every instance
  // tested (avg rank 2.5, worst 5) — by far the most robust single
  // configuration. See SHARED_CACHE_REPORT.md for the data.
  //
  // History of default revisions:
  //   v1 (initial):  cap=1024, ham=1%, warmup=0, pick=linear, expl=0
  //   v2 (sweep1):   cap=256, ham=5%, warmup=5   (combo_loose)
  //   v3 (sweep2):   warmup back to 0            (warmup_5 lost on 37,39,40)
  //   v4 (sweep4):   pick=UNIFORM, expl=25       (won ntil-41 sweep4)
  //   v5 (sweep5):   expl=0, cutoff bump         (current; expl=25 was
  //                  bottom-half on every sweep5 instance)
  //
  // capacity=0 means "auto" -- the palsat driver sets it to 32 x threads
  // before allocating. Explicit --shared-cache-size=N still overrides.
  cfg->capacity         = 0;
  cfg->hamming_percent  = 10;
  cfg->pick_weight      = YSC_PICK_UNIFORM;
  cfg->softmax_temp_x10 = 10;        // T = 1.0
  cfg->replace_full     = YSC_REPLACE_WORSE_ONLY;
  cfg->ham_replace      = YSC_HAM_REPLACE_EQ;
  cfg->warmup           = 0;
  cfg->explore_pct      = 0;
  cfg->insert_mode      = YSC_INSERT_ALWAYS;
  cfg->popularity_pct   = 50;        // sweep7: pop50 top-3 on 3/4 hard
                                     //         instances; faster slot
                                     //         cooling -> more diversity.
}

void yals_shared_cache_config_dump (const YalsSharedCacheConfig * cfg,
                                    FILE * f) {
  static const char * pick_names[]   = {"linear","rank","softmax","uniform","inv"};
  static const char * repl_names[]   = {"worse-only","always","never"};
  static const char * ham_names[]    = {"eq","strict","always"};
  static const char * ins_names[]    = {"always","improved"};
  fprintf (f,
    "c shared-cache config: cap=%d ham_pct=%d pick=%s softmax_T=%.1f "
    "replace=%s ham_replace=%s warmup=%d explore_pct=%d insert=%s popularity_pct=%d\n",
    cfg->capacity, cfg->hamming_percent,
    pick_names[cfg->pick_weight % 5],
    cfg->softmax_temp_x10 / 10.0,
    repl_names[cfg->replace_full % 3],
    ham_names[cfg->ham_replace % 3],
    cfg->warmup, cfg->explore_pct,
    ins_names[cfg->insert_mode % 2],
    cfg->popularity_pct);
}

YalsSharedCache * yals_shared_cache_new (int nworkers,
                                         const YalsSharedCacheConfig * cfg) {
  YalsSharedCache * c = calloc (1, sizeof *c);
  c->cfg = *cfg;
  // capacity <= 0 means auto = 32 * nworkers (palsat driver normally
  // applies this before calling us; this is a defensive fallback).
  if (c->cfg.capacity <= 0) c->cfg.capacity = 32 * nworkers;
  if (c->cfg.capacity < 1) c->cfg.capacity = 1;
  if (c->cfg.hamming_percent < 0) c->cfg.hamming_percent = 0;
  if (c->cfg.softmax_temp_x10 < 1) c->cfg.softmax_temp_x10 = 1;
  if (c->cfg.warmup < 0) c->cfg.warmup = 0;
  if (c->cfg.explore_pct < 0) c->cfg.explore_pct = 0;
  if (c->cfg.explore_pct > 100) c->cfg.explore_pct = 100;
  if (c->cfg.popularity_pct < 0) c->cfg.popularity_pct = 0;
  if (c->cfg.popularity_pct > 100) c->cfg.popularity_pct = 100;
  c->nworkers = nworkers;
  c->vals = calloc (c->cfg.capacity, sizeof (Word *));
  c->mins = calloc (c->cfg.capacity, sizeof (int));
  c->reserved = malloc (c->cfg.capacity * sizeof (int));
  c->pick_count = calloc (c->cfg.capacity, sizeof (long long));
  for (int i = 0; i < c->cfg.capacity; i++) c->reserved[i] = -1;
  c->worker_slot = malloc (nworkers * sizeof (int));
  c->worker_restarts = calloc (nworkers, sizeof (int));
  c->worker_start_cost = malloc (nworkers * sizeof (int));
  for (int i = 0; i < nworkers; i++) {
    c->worker_slot[i] = -1;
    c->worker_start_cost[i] = INT_MAX;
  }
  pthread_mutex_init (&c->lock, 0);
  return c;
}

void yals_shared_cache_delete (YalsSharedCache * c) {
  if (!c) return;
  for (int i = 0; i < c->cfg.capacity; i++) free (c->vals[i]);
  free (c->vals);
  free (c->mins);
  free (c->reserved);
  free (c->worker_slot);
  free (c->worker_restarts);
  free (c->worker_start_cost);
  free (c->pick_count);
  pthread_mutex_destroy (&c->lock);
  free (c);
}

void yals_set_shared_cache (Yals * yals, YalsSharedCache * c) {
  yals->shared_cache = c;
}

void yals_shared_cache_stats (YalsSharedCache * c) {
  if (!c) return;
  fprintf (stdout,
    "c shared cache: capacity %d, used %d, hamming_thresh %d bits "
    "(%d%% of %d vars)\n",
    c->cfg.capacity, c->count, c->hamming_threshold,
    c->cfg.hamming_percent, c->nvars);
  fprintf (stdout,
    "c shared cache: inserts %lld, ham-replaces %lld, worse-replaces %lld\n",
    c->s_inserted, c->s_replaced_ham, c->s_replaced_worse);
  fprintf (stdout,
    "c shared cache: skipped (close-worse %lld, no-room %lld, src-empty %lld, no-improve %lld)\n",
    c->s_skipped_close_worse, c->s_skipped_no_room, c->s_skipped_empty,
    c->s_skipped_no_improve);
  fprintf (stdout,
    "c shared cache: picks %lld (warmup-skip %lld, explore %lld), pick-empty %lld\n",
    c->s_picked, c->s_pick_warmup, c->s_pick_explore, c->s_pick_empty);
  fflush (stdout);
}

static int yals_shared_cache_hamming (const Word * a, const Word * b,
                                      int nwords) {
  int h = 0;
  for (int i = 0; i < nwords; i++)
    h += __builtin_popcount ((unsigned) (a[i] ^ b[i]));
  return h;
}

static void yals_shared_cache_init_dims_locked (YalsSharedCache * c,
                                                int nvars, int nvarwords) {
  if (c->nvarwords) return;
  c->nvars = nvars;
  c->nvarwords = nvarwords;
  int t = (c->cfg.hamming_percent * nvars) / 100;
  if (t < 1 && c->cfg.hamming_percent > 0) t = 1;
  c->hamming_threshold = t;
}

static void yals_shared_cache_release (Yals * yals) {
  YalsSharedCache * c = yals->shared_cache;
  if (!c) return;
  int w = yals->wid;
  if (w < 0 || w >= c->nworkers) return;
  pthread_mutex_lock (&c->lock);
  int slot = c->worker_slot[w];
  if (slot >= 0) {
    c->reserved[slot] = -1;
    c->worker_slot[w] = -1;
  }
  pthread_mutex_unlock (&c->lock);
}

// Decide whether to keep the inserted assignment given a Hamming-close
// existing entry.
static int yals_shared_cache_ham_should_replace (int policy,
                                                 int new_cost,
                                                 int old_cost) {
  switch (policy) {
    case YSC_HAM_REPLACE_STRICT: return new_cost <  old_cost;
    case YSC_HAM_REPLACE_ALWAYS: return 1;
    case YSC_HAM_REPLACE_EQ:
    default:                     return new_cost <= old_cost;
  }
}

static void yals_shared_cache_insert (Yals * yals) {
  YalsSharedCache * c = yals->shared_cache;
  if (!c) return;
  // Nothing useful to insert until at least one flip / save_new_minimum.
  if (yals->stats.tmp == INT_MAX) {
    pthread_mutex_lock (&c->lock);
    c->s_skipped_empty++;
    pthread_mutex_unlock (&c->lock);
    return;
  }
  const Word * src = yals->tmp;
  int min = yals->stats.tmp;
  pthread_mutex_lock (&c->lock);
  yals_shared_cache_init_dims_locked (c, yals->nvars, yals->nvarwords);

  // Insert gating: only insert if we improved over what this try started with.
  if (c->cfg.insert_mode == YSC_INSERT_IMPROVED) {
    int w = yals->wid;
    int start = (w >= 0 && w < c->nworkers) ? c->worker_start_cost[w] : INT_MAX;
    if (start != INT_MAX && min >= start) {
      c->s_skipped_no_improve++;
      pthread_mutex_unlock (&c->lock);
      return;
    }
  }
  size_t bytes = c->nvarwords * sizeof (Word);

  // 1. Hamming-close unreserved entry?  (skip search if threshold == 0)
  int close = -1;
  if (c->hamming_threshold > 0) {
    for (int i = 0; i < c->cfg.capacity; i++) {
      if (!c->vals[i]) continue;
      if (c->reserved[i] >= 0) continue;
      int h = yals_shared_cache_hamming (src, c->vals[i], c->nvarwords);
      if (h < c->hamming_threshold) { close = i; break; }
    }
  }
  if (close >= 0) {
    if (yals_shared_cache_ham_should_replace (c->cfg.ham_replace,
                                              min, c->mins[close])) {
      memcpy (c->vals[close], src, bytes);
      c->mins[close] = min;
      c->pick_count[close] = 0;       // fresh content -> reset popularity
      c->s_replaced_ham++;
    } else {
      c->s_skipped_close_worse++;
    }
    pthread_mutex_unlock (&c->lock);
    return;
  }

  // 2. Free slot?
  int free_slot = -1;
  for (int i = 0; i < c->cfg.capacity; i++) {
    if (!c->vals[i]) { free_slot = i; break; }
  }
  if (free_slot >= 0) {
    c->vals[free_slot] = malloc (bytes);
    memcpy (c->vals[free_slot], src, bytes);
    c->mins[free_slot] = min;
    c->reserved[free_slot] = -1;
    c->pick_count[free_slot] = 0;     // new content -> reset popularity
    c->count++;
    c->s_inserted++;
    pthread_mutex_unlock (&c->lock);
    return;
  }

  // 3. Cache full + no ham-match. Replacement per policy.
  if (c->cfg.replace_full == YSC_REPLACE_NEVER) {
    c->s_skipped_no_room++;
    pthread_mutex_unlock (&c->lock);
    return;
  }
  int worst = -1, worst_cost = -1;
  int require_worse = (c->cfg.replace_full == YSC_REPLACE_WORSE_ONLY);
  for (int i = 0; i < c->cfg.capacity; i++) {
    if (c->reserved[i] >= 0) continue;
    if (require_worse && c->mins[i] < min) continue;
    if (c->mins[i] > worst_cost) {
      worst_cost = c->mins[i];
      worst = i;
    }
  }
  if (worst >= 0) {
    memcpy (c->vals[worst], src, bytes);
    c->mins[worst] = min;
    c->pick_count[worst] = 0;         // fresh content -> reset popularity
    c->s_replaced_worse++;
  } else {
    c->s_skipped_no_room++;
  }
  pthread_mutex_unlock (&c->lock);
}

// Build a per-slot weight given the configured pick scheme. Slots that
// are not available (NULL or reserved) get weight 0.
// `weights` is sized [capacity]. Returns the sum of weights.
static double yals_shared_cache_build_weights (YalsSharedCache * c,
                                               double * weights) {
  int cap = c->cfg.capacity;
  int maxc = -1;
  int navail = 0;
  for (int i = 0; i < cap; i++) {
    weights[i] = 0.0;
    if (!c->vals[i] || c->reserved[i] >= 0) continue;
    if (c->mins[i] > maxc) maxc = c->mins[i];
    navail++;
  }
  if (!navail) return 0.0;
  // For rank scheme we need a sorted list of (cost, idx) over avail.
  // For other schemes we compute directly.
  if (c->cfg.pick_weight == YSC_PICK_RANK) {
    // O(n^2) ranking, fine for cap <= ~4096.
    // Each available slot's rank = number of available slots with strictly
    // smaller cost (or equal, with ties broken by index). Weight = N - rank.
    for (int i = 0; i < cap; i++) {
      if (!c->vals[i] || c->reserved[i] >= 0) continue;
      int rank = 0;
      for (int j = 0; j < cap; j++) {
        if (j == i || !c->vals[j] || c->reserved[j] >= 0) continue;
        if (c->mins[j] < c->mins[i] ||
            (c->mins[j] == c->mins[i] && j < i)) rank++;
      }
      weights[i] = (double) (navail - rank);
    }
  } else {
    double temp = c->cfg.softmax_temp_x10 / 10.0;
    if (temp < 0.1) temp = 0.1;
    for (int i = 0; i < cap; i++) {
      if (!c->vals[i] || c->reserved[i] >= 0) continue;
      int cost = c->mins[i];
      double w;
      switch (c->cfg.pick_weight) {
        case YSC_PICK_UNIFORM: w = 1.0; break;
        case YSC_PICK_INV:     w = 1.0 / (cost + 1.0); break;
        case YSC_PICK_SOFTMAX: w = exp ((double)(maxc - cost) / temp); break;
        case YSC_PICK_LINEAR:
        default:               w = (double) (maxc - cost + 1); break;
      }
      weights[i] = w;
    }
  }
  // Anti-clustering: divide each slot's weight by (1 + alpha * pick_count).
  // alpha = popularity_pct / 100. Slots that have been picked many times since
  // their content was last refreshed get exponentially less attractive.
  if (c->cfg.popularity_pct > 0) {
    double alpha = c->cfg.popularity_pct / 100.0;
    for (int i = 0; i < cap; i++) {
      if (weights[i] <= 0) continue;
      weights[i] /= (1.0 + alpha * (double) c->pick_count[i]);
    }
  }
  double total = 0.0;
  for (int i = 0; i < cap; i++) total += weights[i];
  return total;
}

// Returns 1 if a pick was made and yals->vals was overwritten.
static int yals_shared_cache_pick (Yals * yals) {
  YalsSharedCache * c = yals->shared_cache;
  if (!c) return 0;
  int w = yals->wid;
  if (w < 0 || w >= c->nworkers) return 0;

  pthread_mutex_lock (&c->lock);
  // Per-worker warm-up: first N restarts skip the shared pick.
  int rcount = c->worker_restarts[w]++;
  if (rcount < c->cfg.warmup) {
    c->s_pick_warmup++;
    pthread_mutex_unlock (&c->lock);
    return 0;
  }
  if (!c->nvarwords || c->count == 0) {
    c->s_pick_empty++;
    pthread_mutex_unlock (&c->lock);
    return 0;
  }

  int cap = c->cfg.capacity;
  int picked = -1;
  int navail = 0;
  for (int i = 0; i < cap; i++) {
    if (!c->vals[i] || c->reserved[i] >= 0) continue;
    navail++;
  }
  if (!navail) {
    c->s_pick_empty++;
    pthread_mutex_unlock (&c->lock);
    return 0;
  }

  int use_explore = 0;
  if (c->cfg.explore_pct > 0) {
    unsigned r = yals_rand (yals) % 100u;
    if ((int) r < c->cfg.explore_pct) use_explore = 1;
  }

  if (use_explore) {
    unsigned pick_idx = yals_rand (yals) % (unsigned) navail;
    unsigned seen = 0;
    for (int i = 0; i < cap; i++) {
      if (!c->vals[i] || c->reserved[i] >= 0) continue;
      if (seen == pick_idx) { picked = i; break; }
      seen++;
    }
    c->s_pick_explore++;
  } else {
    double * weights = malloc (cap * sizeof (double));
    double total = yals_shared_cache_build_weights (c, weights);
    if (total > 0) {
      // Two yals_rand calls give 64 bits of entropy.
      unsigned hi = yals_rand (yals);
      unsigned lo = yals_rand (yals);
      double u = (((double) hi) * 4294967296.0 + (double) lo) /
                 (4294967296.0 * 4294967296.0);
      double target = u * total;
      double acc = 0.0;
      for (int i = 0; i < cap; i++) {
        if (weights[i] <= 0) continue;
        acc += weights[i];
        if (acc >= target) { picked = i; break; }
      }
      // numerical safety: fall back to any available.
      if (picked < 0) {
        for (int i = 0; i < cap; i++) {
          if (c->vals[i] && c->reserved[i] < 0) { picked = i; break; }
        }
      }
    }
    free (weights);
  }

  if (picked >= 0) {
    c->reserved[picked] = w;
    c->worker_slot[w] = picked;
    c->worker_start_cost[w] = c->mins[picked];
    c->pick_count[picked]++;
    size_t bytes = c->nvarwords * sizeof (Word);
    memcpy (yals->vals, c->vals[picked], bytes);
    c->s_picked++;
  } else {
    c->s_pick_empty++;
    // No pick made: this try will run from whatever yals_pick_assignment
    // left in vals. Treat its starting cost as unknown -> never improvable.
    c->worker_start_cost[w] = INT_MAX;
  }
  pthread_mutex_unlock (&c->lock);
  return picked >= 0 ? 1 : 0;
}

// Hook called from yals_restart_inner: release previous reservation,
// insert best-of-just-finished try, pick a new starting assignment.
// Returns 1 iff yals->vals was overwritten (caller must reapply trailing
// bits + units and rebuild satcounters).
static int yals_shared_cache_cycle (Yals * yals) {
  if (!yals->shared_cache) return 0;
  yals_shared_cache_release (yals);
  yals_shared_cache_insert (yals);
  return yals_shared_cache_pick (yals);
}

/*------------------------------------------------------------------------*/

static void yals_cache_assignment (Yals * yals) {
  int min, other_min, cachemax, cachemin, cachemincount, cachemaxcount;
  unsigned start, delta, i, j, ncache, rpos;
  Word sig, other_sig, * other_vals;
  size_t bytes;
#ifndef NDEBUG
  int count;
#endif

  if (!yals->opts.cachemin.val) return;
  sig = yals_sig (yals);
  ncache = COUNT (yals->cache);
  for (i = 0; i < ncache; i++) {
    other_sig = PEEK (yals->sigs, i);
    yals->stats.sig.search++;
    if (other_sig != sig) { yals->stats.sig.neg++; continue; }
    other_vals = PEEK (yals->cache, i);
    for (j = 0; j < yals->nvarwords; j++)
      if (other_vals[j] != yals->tmp[j]) break;
    if (j == yals->nvarwords) {
      yals_msg (yals, 2, "current assigment already in cache");
      yals->stats.cache.skipped++;
      yals->stats.sig.truepos++;
      return;
    }
    yals->stats.sig.falsepos++;
  }

  cachemin = INT_MAX, cachemax = -1;
  cachemaxcount = cachemincount = 0;
  for (j = 0; j < ncache; j++) {
    other_min = PEEK (yals->mins, j);
    if (other_min < cachemin) cachemin = other_min, cachemincount = 0;
    if (other_min > cachemax) cachemax = other_min, cachemaxcount = 0;
    if (other_min == cachemin) cachemincount++;
    if (other_min == cachemax) cachemaxcount++;
  }
  yals_msg (yals, 2,
    "cache of size %d minimum %d (%d = %.0f%%) maximum %d (%d = %.0f%%)",
    ncache,
    cachemin, cachemincount, yals_pct (cachemincount, ncache),
    cachemax, cachemaxcount, yals_pct (cachemaxcount, ncache));

  min = yals->stats.tmp;
  yals_msg (yals, 4, "nunsat %d min %d", yals_nunsat (yals), min);
  assert (min <= yals_nunsat (yals));
  bytes = yals->nvarwords * sizeof (Word);
  if (!yals->cachesizetarget) {
    yals->cachesizetarget = yals->opts.cachemin.val;
    assert (yals->cachesizetarget);
    yals_msg (yals, 2,
      "initial cache size target of %d",
      yals->cachesizetarget);
  }

  if (ncache < yals->cachesizetarget) {
PUSH_ASSIGNMENT:
    yals_msg (yals, 2,
      "pushing current assigment with minimum %d in cache as assignment %d",
      min, ncache);
    NEWN (other_vals, yals->nvarwords);
    memcpy (other_vals, yals->tmp, bytes);
    PUSH (yals->cache, other_vals);
    PUSH (yals->sigs, sig);
    PUSH (yals->mins, min);
    yals->stats.cache.inserted++;
  } else {
    assert (ncache == yals->cachesizetarget);
    if (ncache == 1) start = delta = 0;
    else {
      start = yals_rand_mod (yals, ncache);
      delta = yals_rand_mod (yals, ncache - 1) + 1;
      while (yals_gcd (ncache, delta) != 1)
delta--;
    }
    rpos = ncache;
    j = start;
#ifndef NDEBUG
    count = 0;
#endif
    do {
      other_min = PEEK (yals->mins, j);
      assert (other_min >= cachemin);
      assert (other_min <= cachemax);
      if (other_min == cachemax && other_min > min) rpos = j;
      j += delta;
      if (j >= ncache) j -= ncache, assert (j < ncache);
#ifndef NDEBUG
      count++;
#endif
    } while (j != start);
    assert (count == ncache);

    if (rpos < ncache) {
      assert (min < cachemax);
      assert (PEEK (yals->mins, rpos) == cachemax);
      yals_msg (yals, 2,
"replacing cached %d (minimum %d) better minimum %d",
rpos, cachemax, min);
      other_vals = PEEK (yals->cache, rpos);
      memcpy (other_vals, yals->tmp, bytes);
      POKE (yals->mins, rpos, min);
      POKE (yals->sigs, rpos, sig);
      yals->stats.cache.replaced++;
    } else if (min > cachemax ||
               (cachemin < cachemax && min == cachemax)) {
DO_NOT_CACHE_ASSSIGNEMNT:
      yals_msg (yals, 2,
"local minimum %d not cached needs %d",
min, cachemax-1);
      yals->stats.cache.skipped++;
    } else {
      assert (min == cachemin);
      assert (min == cachemax);
      assert (min == yals->stats.best);
      if (yals->cachesizetarget < yals->opts.cachemax.val) {
yals->cachesizetarget *= 2;
if (yals->cachesizetarget < ncache) {
 yals->cachesizetarget = ncache;
 goto DO_NOT_CACHE_ASSSIGNEMNT;
}
yals_msg (yals, 2,
 "new cache size target of %d",
 yals->cachesizetarget);
goto PUSH_ASSIGNMENT;
      } else goto DO_NOT_CACHE_ASSSIGNEMNT;
    }
  }
}

void yals_remove_trailing_bits (Yals * yals) {
  unsigned i;
  Word mask;
  if (!yals->nvarwords) return;
  i = yals->nvars & BITMAPMASK;
  mask = ((Word)1) << (i + 1);
  yals->vals[yals->nvarwords-1] &= mask - 1;
}

void yals_set_units (Yals * yals) {
  const Word * eow, * c, * s;
  Word * p = yals->vals, tmp;
  eow = p + yals->nvarwords;
  c = yals->clear;
  s = yals->set;
  while (p < eow) {
    tmp = *p;
    tmp &= *c++;
    tmp |= *s++;
    *p++ = tmp;
  }
  assert (s == yals->set + yals->nvarwords);
  assert (c == yals->clear + yals->nvarwords);
}

static void yals_setphases (Yals * yals) {
  int i, idx, lit;
  yals_msg (yals, 1,
    "forcing %d initial phases", (int) COUNT (yals->phases));
  for (i = 0; i < COUNT (yals->phases); i++) {
    lit = PEEK (yals->phases, i);
    assert (lit);
    idx = ABS (lit);
    if (idx >= yals->nvars) {
      LOG ("skipping setting phase of %d", lit);
      continue;
    }
    LOG ("setting phase of %d", lit);
    if (lit > 0) SETBIT (yals->vals, yals->nvarwords, idx);
    else CLRBIT (yals->vals, yals->nvarwords, idx);
  }
  RELEASE (yals->phases);
}

static void yals_pick_assignment (Yals * yals, int initial) {
  int idx, pos, neg, i, nvars = yals->nvars, ncache;
  size_t bytes = yals->nvarwords * sizeof (Word);
  const int vl = 1 + !initial;
  if (!initial && yals->opts.best.val) {
    yals->stats.pick.best++;
    yals_msg (yals, vl, "picking previous best assignment");
    memcpy (yals->vals, yals->best, bytes);
  } else if (!initial && yals->opts.keep.val) {
    yals->stats.pick.keep++;
    yals_msg (yals, vl, "picking current assignment (actually keeping it)");
  } else if (!initial &&
             yals->strat.cached &&
    (ncache = COUNT (yals->cache)) > 0) {
    if (!yals->opts.cacheduni.val)  {
      assert (EMPTY (yals->cands));
      assert (EMPTY (yals->scores));
      for (i = 0; i < ncache; i++) {
int min = PEEK (yals->mins, i);
assert (min >= 0);
PUSH (yals->cands, i);
PUSH (yals->scores, min);
      }
      pos = yals_pick_by_score (yals);
      CLEAR (yals->scores);
      CLEAR (yals->cands);
    } else pos = yals_rand_mod (yals, ncache);
    yals->stats.pick.cached++;
    yals_msg (yals, vl,
      "picking cached assignment %d with minimum %d",
      pos, PEEK (yals->mins, pos));
    memcpy (yals->vals, PEEK (yals->cache, pos), bytes);
  } else if (yals->strat.pol < 0) {
    yals->stats.pick.neg++;
    yals_msg (yals, vl, "picking all negative assignment");
    memset (yals->vals, 0, bytes);
  } else if (yals->strat.pol > 0) {
    yals->stats.pick.pos++;
    yals_msg (yals, vl, "picking all positive assignment");
    memset (yals->vals, 0xff, bytes);
  } else {
    yals->stats.pick.rnd++;
    yals_msg (yals, vl, "picking new random assignment");
    for (i = 0; i < yals->nvarwords; i++)
      yals->vals[i] = yals_rand (yals);
  }
  yals_remove_trailing_bits (yals);
  if (initial) yals_setphases (yals);
  yals_set_units (yals);
  if (yals->opts.verbose.val <= 2) return;
  pos = neg = 0;
  for (idx = 1; idx < nvars; idx++)
    if (GETBIT (yals->vals, yals->nvarwords, idx)) pos++;
  neg = nvars - pos;
  yals_msg (yals, vl,
    "new full assignment %d positive %d negative", pos, neg);
}

static void yals_log_assignment (Yals * yals) {
#ifndef NDEBUG
  int idx;
  if (!yals->opts.logging.val) return;
  for (idx = 1; idx < yals->nvars; idx++) {
    int lit = yals_val (yals, idx) ? idx : -idx;
    LOG ("assigned %d", lit);
  }
#endif
}

static unsigned yals_len_to_weight (Yals * yals, int len) {
  const int uni = yals->strat.uni;
  const int weight = yals->strat.weight;
  unsigned w;

  if (uni > 0) w = weight;
  else if (uni < 0) w = MIN (len, weight);
  else w = MAX (weight - len, 1);

  return w;
}

/*
  Given an assignment, initialize weights and satcnt for all constraints.

  Check the global invariants after initialization.
*/
void yals_update_sat_and_unsat (Yals * yals) {
  int lit, cidx, len, cappedlen, crit, bound;
  const int * lits, * p;
  unsigned satcnt;
  yals_log_assignment (yals);
  yals_reset_unsat (yals);

  yals_reset_ddfw (yals);
  
  for (len = 1; len <= MAXLEN; len++)
    yals->weights[len] = yals_len_to_weight (yals, len); // probsat weights by length
  if (yals->crit)
    memset (yals->weightedbreak, 0, 2*yals->nvars*sizeof(int));

  LOG ("UPDATE clauses");
  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    satcnt = 0;
    lits = yals_lits (yals, cidx);
    crit = 0;
    for (p = lits; (lit = *p); p++) {
      if (!yals_val (yals, lit)) continue;
      crit ^= lit;
      satcnt++;
    }

    //if (!yals->ddfw.init_weight_done)
    yals_ddfw_update_lit_weights_at_start (yals, cidx, satcnt, crit);
    LOG ("updated lit weights");
    // gets handled with yals_enqueue
    // if (!satcnt)
    //   yals_ddfw_update_uvars (yals, cidx);
   
    yals->ddfw.sat_count_in_clause [cidx] = satcnt;

    if (yals->crit) yals->crit[cidx] = crit;

    len = p - lits;
    cappedlen = MIN (len, MAXLEN);
    LOGCIDX (cidx,
       "sat count %u length %d weight %u for",
       satcnt, len, yals->weights[cappedlen]);
    yals_setsatcnt (yals, cidx, satcnt);
    if (!satcnt) {
      yals_enqueue (yals, cidx, TYPECLAUSE);
      LOGCIDX (cidx, "broken");
    } else if (yals->crit && satcnt == 1 && !yals->ddfw.ddfw_active)
      yals_inc_weighted_break (yals, yals->crit[cidx], cappedlen);
  }

  LOG ("UPDATE constraints");
  // cardinality constraints
  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    satcnt = 0;
    lits = yals_card_lits (yals, cidx);
    bound = yals_card_bound (yals, cidx);
    crit = 0;
    for (p = lits; (lit = *p); p++) {
      if (!yals_val (yals, lit)) continue;
      // crit ^= lit;
      satcnt++;
    }

    yals->ddfw.card_sat_count_in_clause [cidx] = (int) satcnt;

    // set critical literals if the satcnt less than or equals the bound
    if (satcnt <= bound) {
      LOGCARDCIDX (cidx, "critical, sorting");
      yals_card_sort_sat (yals, cidx);
    }   

    len = p - lits;
    cappedlen = MIN (len, MAXLEN);
    LOGCARDCIDX (cidx,
       "sat count %u length %d weight %u bound %d for",
       satcnt, len, yals->ddfw.ddfw_card_weights[cidx], bound);
    yals_card_setsatcnt (yals, cidx, satcnt);
    if (satcnt < bound) {
      yals_enqueue (yals, cidx, TYPECARDINALITY);
      LOGCARDCIDX (cidx, "broken");
    }
    if (yals->crit && satcnt <= bound && !yals->ddfw.ddfw_active) // satisfied literals are all critical
      yals_card_inc_all_weighted_break (yals, cidx, cappedlen);

    //if (!yals->ddfw.init_weight_done)
    yals_card_ddfw_update_lit_weights_at_start (yals, cidx, satcnt, bound);

    // gets handled with yals_enqueue
    // if (satcnt < bound) // falsified constraint
    //   yals_card_ddfw_update_uvars (yals, cidx);
  }

  yals->ddfw.init_weight_done = 1;
  yals_check_global_satisfaction_invariant (yals);
}

static void yals_init_weight_to_score_table (Yals * yals) {
  double cb, invcb, score, eps;
  const double start = 1e150;
  int maxlen = yals->maxlen;
  unsigned i;

  // probSAT SC'13 values:

       if (maxlen <= 3) cb = 2.5; // from Adrian's thesis ...
  else if (maxlen <= 4) cb = 2.85;
  else if (maxlen <= 5) cb = 3.7;
  else if (maxlen <= 6) cb = 5.1;
  else                  cb = 5.4;

  yals_msg (yals, 1,
    "exponential base cb = %f for maxlen %d",
    cb, maxlen);

  eps = 0;
  score = start;
  for (i = 0; score; i++) {
    assert (i < 100000);
    // LOG ("exp2(-%d) = %g", i, score);
    PUSH (yals->exp.table.two, score);
    eps = score;
    score *= .5;
  }
  assert (eps > 0);
  assert (i == COUNT (yals->exp.table.two));
  yals->exp.max.two = i;
  yals->exp.eps.two = eps;
  yals_msg (yals, 1, "exp2(<= %d) = %g", -i, eps);

  invcb = 1.0 / cb;
  assert (invcb < 1.0);
  score = start;
  eps = 0.0;
  for (i = 0; score; i++) {
    assert (i < 1000000);
    // LOG ("pow(%f,-%d) = %g", cb, i, score);
    PUSH (yals->exp.table.cb, score);
    eps = score;
    score *= invcb;
  }
  assert (eps > 0);
  assert (i == COUNT (yals->exp.table.cb));
  yals->exp.max.cb = i;
  yals->exp.eps.cb = eps;
  yals_msg (yals, 1, "pow(%f,(<= %d)) = %g", cb, -i, eps);
}

/*------------------------------------------------------------------------*/

static void yals_connect (Yals * yals) {
  int idx, n, lit, nvars = yals->nvars, * count, cidx, sign;
  long long sumoccs, sumlen; int minoccs, maxoccs, minlen, maxlen;
  int * occsptr, occs, len, lits, maxidx, nused, uniform;
  int nclauses, nbin, ntrn, nquad, nlarge;
  const int * p,  * q;

  LOG ("CONNECT Clauses");

  // connect clauses
  FIT (yals->cdb);
  RELEASE (yals->mark);
  RELEASE (yals->clause);

  maxlen = 0;
  sumlen = 0;
  minlen = INT_MAX;
  nclauses = nbin = ntrn = nquad = nlarge = 0;

  yals->card_crit = 1;

  for (p = yals->cdb.start; p < yals->cdb.top; p = q + 1) {
    for (q = p; *q; q++)
      ;
    len = q - p;

         if (len == 2) nbin++;
    else if (len == 3) ntrn++;
    else if (len == 4) nquad++;
    else               nlarge++;

    nclauses++;

    sumlen += len;
    if (len > maxlen) maxlen = len;
    if (len < minlen) minlen = len;
  }

  yals_msg (yals, 1,
    "found %d binary, %d ternary and %d large clauses",
    nbin, ntrn, nclauses - nbin - ntrn);

  yals_msg (yals, 1,
    "size of literal stack %d (%d for large clauses only)",
    (int) COUNT (yals->cdb),
    ((int) COUNT (yals->cdb)) - 3*nbin - 4*ntrn);

  yals->maxlen = maxlen;
  yals->minlen = minlen;
#ifndef NYALSTATS
  yals->stats.nincdec = MAX (maxlen + 1, 3);
  NEWN (yals->stats.inc, yals->stats.nincdec);
  NEWN (yals->stats.dec, yals->stats.nincdec);
  assert (!yals->stats.dec[0]);
#endif

  if ((INT_MAX >> LENSHIFT) < nclauses)
    yals_abort (yals,
      "maximum number of clauses %d exceeded",
      (INT_MAX >> LENSHIFT));

  yals->nclauses = nclauses;
  yals->nbin = nbin;
  yals->ntrn = ntrn;
  yals_msg (yals, 1, "connecting %d clauses", nclauses);
  NEWN (yals->lits, nclauses);
  NEWN (yals->hard_clause_ids, nclauses);

  lits = 0;
  for (cidx = 0; cidx < nclauses; cidx++) {
    yals->lits[cidx] = lits;
    while (PEEK (yals->cdb, lits)) lits++;
    lits++;
    if (yals->using_maxs_weights) {
    if (PEEK (yals->maxs_clause_weights, cidx) == yals->maxs_hard_weight)
      yals->hard_clause_ids[cidx] = 1;
    else
      yals->hard_clause_ids[cidx] = 0;
    }
  }
  assert (lits == COUNT (yals->cdb));

  NEWN (yals->weights, MAXLEN + 1);

  NEWN (count, 2*nvars);
  count += nvars;

  maxidx = maxoccs = -1;
  minoccs = INT_MAX;
  sumoccs = 0;

  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    for (p = yals_lits (yals, cidx); (lit = *p); p++) {
      idx = ABS (lit);
      if (idx > maxidx) maxidx = idx;
      count[lit]++;
    }
  }

  occs = 0;
  nused = 0;
  for (lit = 1; lit < nvars; lit++) {
    int pos = count[lit], neg = count[-lit], sum = pos + neg;
    occs += sum + 2;
    if (sum) nused++;
  }

  assert (nused <= nvars);
  if (nused == nvars)
    yals_msg (yals, 1, "all variables occur");
  else
    yals_msg (yals, 1,
      "%d variables used out of %d, %d do not occur %.0f%%",
      nused, nvars, nvars - nused, yals_pct (nvars-nused, nvars));

  yals->noccs = occs;
  LOG ("size of occurrences stack %d", occs);
  NEWN (yals->occs, yals->noccs);

  NEWN (yals->refs, 2*nvars);

  occs = 0;
  for (lit = 1; lit < nvars; lit++) {
    n = count[lit];
    LOG ("literal %d occurs %d times", lit, n);
    *yals_refs (yals, lit) = occs;
    occs += n, yals->occs[occs++] = -1;
    n = count[-lit];
    LOG ("literal %d occurs %d times", -lit, n);
    *yals_refs (yals, -lit) = occs;
    occs += n, yals->occs[occs++] = -1;
  }
  assert (occs == yals->noccs);

  yals->avglen = yals_avg (sumlen, yals->nclauses);

  if (minlen == maxlen) {
    yals_msg (yals, 1,
      "all %d clauses are of uniform length %d",
      yals->nclauses, maxlen);
  } else if (maxlen >= 0) {
    yals_msg (yals, 1,
      "average clause length %.2f (min %d, max %d)",
      yals->avglen, minlen, maxlen);
    yals_msg (yals, 2,
      "%d binary %.0f%%, %d ternary %.0f%% ",
      nbin, yals_pct (nbin, yals->nclauses),
      ntrn, yals_pct (ntrn, yals->nclauses));
    yals_msg (yals, 2,
      "%d quaterny %.0f%%, %d large clauses %.0f%%",
      nquad, yals_pct (nquad, yals->nclauses),
      nlarge, yals_pct (nlarge, yals->nclauses));
  }

  if (minlen == maxlen && !yals->opts.toggleuniform.val) uniform = 1;
  else if (minlen != maxlen && yals->opts.toggleuniform.val) uniform = 1;
  else uniform = 0;

  if (uniform) {
    yals_msg (yals, 1,
      "using uniform strategy for clauses of length %d", maxlen);
    yals->uniform = maxlen;
  } else {
    yals_msg (yals, 1, "using standard non-uniform strategy");
    yals->uniform = 0;
  }

  yals_msg (yals, 1,
    "clause variable ratio %.3f = %d / %d",
    yals_avg (nclauses, nused), nclauses, nused);

  for (idx = 1; idx < nvars; idx++)
    for (sign = 1; sign >= -1; sign -= 2) {
      lit = sign * idx;
      int occs = count[lit] + count[-lit];
      if (!occs) continue;
      sumoccs += occs;
      if (occs > maxoccs) maxoccs = occs;
      if (occs < minoccs) minoccs = occs;
    }

  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    p = yals_lits (yals, cidx);
    len = 0;
    while (len < MAXLEN && p[len]) len++;
    while ((lit = *p++)) {
      occsptr = yals_refs (yals, lit);
      occs = *occsptr;
      assert_valid_occs (occs);
      assert (!yals->occs[occs]);
      yals->occs[occs] = (cidx << LENSHIFT) | len;
      *occsptr = occs + 1;
    }
  }

  for (idx = 1; idx < nvars; idx++) {
    for (sign = 1; sign >= -1; sign -= 2) {
      lit = sign * idx;
      occsptr = yals_refs (yals, lit);
      occs = *occsptr;
      assert_valid_occs (occs);
      assert (yals->occs[occs] == -1);
      n = count[lit];
      assert (occs >= n);
      *occsptr = occs - n;
    }
  }

  count -= nvars;
  DELN (count, 2*nvars);

  yals_msg (yals, 1,
    "average literal occurrence %.2f (min %d, max %d)",
    yals_avg (sumoccs, yals->nvars)/2.0, minoccs, maxoccs);

  yals->pick = 0;

  yals->unsat.usequeue = (yals->pick > 0);

  yals_msg (yals, 1,
    "using %s for unsat clauses",
    yals->unsat.usequeue ? "queue" : "stack");

  if (yals->unsat.usequeue) NEWN (yals->lnk, nclauses);
  else {
    NEWN (yals->pos, nclauses);
    for (cidx = 0; cidx < nclauses; cidx++) yals->pos[cidx] = -1;
    if (yals->using_maxs_weights) {
      NEWN (yals->pos_soft, nclauses);
      for (cidx = 0; cidx < nclauses; cidx++) yals->pos_soft[cidx] = -1;
    }
  }

  yals->nvarwords = (nvars + BITS_PER_WORD - 1) / BITS_PER_WORD;

  yals_msg (yals, 1, "%d x %d-bit words per assignment (%d bytes = %d KB)",
    yals->nvarwords,
    BITS_PER_WORD,
    yals->nvarwords * sizeof (Word),
    (yals->nvarwords * sizeof (Word) >> 10));

  NEWN (yals->set, yals->nvarwords);
  NEWN (yals->clear, yals->nvarwords);
  memset (yals->clear, 0xff, yals->nvarwords * sizeof (Word));
  while (!EMPTY (yals->trail)) {
    lit = POP (yals->trail);
    idx = ABS (lit);
    if (lit < 0) CLRBIT (yals->clear, yals->nvarwords, idx);
    else SETBIT (yals->set, yals->nvarwords, idx);
  }
  RELEASE (yals->trail);

  NEWN (yals->vals, yals->nvarwords);
  NEWN (yals->best, yals->nvarwords);
  NEWN (yals->tmp, yals->nvarwords);
  NEWN (yals->flips, nvars);

  if (maxlen < (1<<8)) {
    yals->satcntbytes = 1;
    NEWN (yals->satcnt1, yals->nclauses);
  } else if (maxlen < (1<<16)) {
    yals->satcntbytes = 2;
    NEWN (yals->satcnt2, yals->nclauses);
  } else {
    yals->satcntbytes = 4;
    NEWN (yals->satcnt4, yals->nclauses);
  }
  yals_msg (yals, 1,
    "need %d bytes per clause for counting satisfied literals",
    yals->satcntbytes);

  if (yals->opts.crit.val) {
    yals_msg (yals, 1,
      "dynamically computing break values on-the-fly "
      "using critical literals");
    NEWN (yals->crit, nclauses);
    NEWN (yals->weightedbreak, 2*nvars);
  } else
    yals_msg (yals, 1, "eagerly computing break values");

  yals_init_weight_to_score_table (yals);
}


// connect cardinality constraints
//  writing as a separate function so it will be easier to debug
void yals_card_connect (Yals * yals) {
  int idx, n, lit, nvars = yals->nvars, * count, cidx, sign;
  long long sumoccs, sumlen; int minoccs, maxoccs, minlen, maxlen;
  int * occsptr, occs, len, lits, maxidx, nused; //, uniform;
  int nclauses, nbin, ntrn, nquad, nlarge;
  const int * p,  * q;

  LOG ("CONNECT Cardinality Constriants");

  FIT (yals->card_cdb);
  RELEASE (yals->mark);
  RELEASE (yals->clause);

  maxlen = 0;
  sumlen = 0;
  minlen = INT_MAX;
  nclauses = nbin = ntrn = nquad = nlarge = 0;

  for (p = yals->card_cdb.start; p < yals->card_cdb.top; p = q + 1) {
    for (q = p; *q; q++)
      ;
    len = q - p - 1; // -1 for the bound at the beggining of the clause

         if (len == 2) nbin++;
    else if (len == 3) ntrn++;
    else if (len == 4) nquad++;
    else               nlarge++;

    nclauses++;

    sumlen += len;
    if (len > maxlen) maxlen = len;
    if (len < minlen) minlen = len;
  }

  yals_msg (yals, 1,
    "found %d binary, %d ternary and %d large cardinality constraints",
    nbin, ntrn, nclauses - nbin - ntrn);

  yals_msg (yals, 1,
    "size of literal stack %d (%d for large cardinality constraints only)",
    (int) COUNT (yals->cdb),
    ((int) COUNT (yals->cdb)) - 3*nbin - 4*ntrn);

  yals->card_maxlen = maxlen;
  yals->card_minlen = minlen;
// #ifndef NYALSTATS
//   yals->stats.nincdec = MAX (maxlen + 1, 3);
//   NEWN (yals->stats.inc, yals->stats.nincdec);
//   NEWN (yals->stats.dec, yals->stats.nincdec);
// #endif

  if ((INT_MAX >> LENSHIFT) < nclauses)
    yals_abort (yals,
      "maximum number of clauses %d exceeded",
      (INT_MAX >> LENSHIFT));

  yals->card_nclauses = nclauses;
  // yals->nbin = nbin;
  // yals->ntrn = ntrn;
  yals_msg (yals, 1, "connecting %d cardinality constraints", nclauses);
  NEWN (yals->card_lits, nclauses);
  NEWN (yals->hard_card_ids, nclauses);

  // have cidx point to bound of each clause
  lits = 0;
  for (cidx = 0; cidx < nclauses; cidx++) {
    yals->card_lits[cidx] = lits;
    while (PEEK (yals->card_cdb, lits)) lits++;
    lits++;
    if (yals->using_maxs_weights) {
    if (PEEK (yals->maxs_card_weights, cidx) == yals->maxs_hard_weight)
      yals->hard_card_ids[cidx] = 1;
    else
      yals->hard_card_ids[cidx] = 0;
    }
  }
  assert (lits == COUNT (yals->card_cdb));

  // NEWN (yals->weights, MAXLEN + 1);

  NEWN (count, 2*nvars);
  count += nvars;

  maxidx = maxoccs = -1;
  minoccs = INT_MAX;
  sumoccs = 0;

  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    for (p = yals_card_lits (yals, cidx); (lit = *p); p++) {
      idx = ABS (lit);
      if (idx > maxidx) maxidx = idx;
      count[lit]++;
    }
  }

  occs = 0;
  nused = 0;
  for (lit = 1; lit < nvars; lit++) {
    int pos = count[lit], neg = count[-lit], sum = pos + neg;
    occs += sum + 2;
    if (sum) nused++;
  }

  assert (nused <= nvars);
  if (nused == nvars)
    yals_msg (yals, 1, "all variables occur in cardinality constraints");
  else
    yals_msg (yals, 1,
      "%d variables used out of %d, %d do not occur in cardinality constraints %.0f%%",
      nused, nvars, nvars - nused, yals_pct (nvars-nused, nvars));

  yals->card_noccs = occs;
  LOG ("size of occurrences stack %d", occs);
  NEWN (yals->card_occs, yals->card_noccs);

  NEWN (yals->card_refs, 2*nvars);

  occs = 0;
  for (lit = 1; lit < nvars; lit++) {
    n = count[lit];
    LOG ("literal %d occurs %d times", lit, n);
    *yals_card_refs (yals, lit) = occs;
    occs += n, yals->card_occs[occs++] = -1;
    n = count[-lit];
    LOG ("literal %d occurs %d times", -lit, n);
    *yals_card_refs (yals, -lit) = occs;
    occs += n, yals->card_occs[occs++] = -1;
  }
  assert (occs == yals->card_noccs);

  yals->card_avglen = yals_avg (sumlen, yals->nclauses);

  // if (minlen == maxlen) {
  //   yals_msg (yals, 1,
  //     "all %d clauses are of uniform length %d",
  //     yals->nclauses, maxlen);
  // } else if (maxlen >= 0) {
  //   yals_msg (yals, 1,
  //     "average clause length %.2f (min %d, max %d)",
  //     yals->avglen, minlen, maxlen);
  //   yals_msg (yals, 2,
  //     "%d binary %.0f%%, %d ternary %.0f%% ",
  //     nbin, yals_pct (nbin, yals->nclauses),
  //     ntrn, yals_pct (ntrn, yals->nclauses));
  //   yals_msg (yals, 2,
  //     "%d quaterny %.0f%%, %d large clauses %.0f%%",
  //     nquad, yals_pct (nquad, yals->nclauses),
  //     nlarge, yals_pct (nlarge, yals->nclauses));
  // }

  // if (minlen == maxlen && !yals->opts.toggleuniform.val) uniform = 1;
  // else if (minlen != maxlen && yals->opts.toggleuniform.val) uniform = 1;
  // else uniform = 0;

  // if (uniform) {
  //   yals_msg (yals, 1,
  //     "using uniform strategy for clauses of length %d", maxlen);
  //   yals->uniform = maxlen;
  // } else {
  //   yals_msg (yals, 1, "using standard non-uniform strategy");
  //   yals->uniform = 0;
  // }

  // yals_msg (yals, 1,
  //   "clause variable ratio %.3f = %d / %d",
  //   yals_avg (nclauses, nused), nclauses, nused);

  for (idx = 1; idx < nvars; idx++)
    for (sign = 1; sign >= -1; sign -= 2) {
      lit = sign * idx;
      int occs = count[lit] + count[-lit];
      if (!occs) continue;
      sumoccs += occs;
      if (occs > maxoccs) maxoccs = occs;
      if (occs < minoccs) minoccs = occs;
    }

  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    p = yals_card_lits (yals, cidx);
    len = 0;
    while (p[len]) len++;
    // actual length
    PUSH (yals->card_size, len);

    len = 0;
    while (len < MAXLEN && p[len]) len++;
    while ((lit = *p++)) {
      occsptr = yals_card_refs (yals, lit);
      occs = *occsptr;
      // assert_valid_occs (occs);
      assert (!yals->card_occs[occs]);
      yals->card_occs[occs] = (cidx << LENSHIFT) | len;
      *occsptr = occs + 1;
    }
    
  }

  for (idx = 1; idx < nvars; idx++) {
    for (sign = 1; sign >= -1; sign -= 2) {
      lit = sign * idx;
      occsptr = yals_card_refs (yals, lit);
      occs = *occsptr;
      // assert_valid_occs (occs);
      assert (yals->card_occs[occs] == -1);
      n = count[lit];
      assert (occs >= n);
      *occsptr = occs - n;
    }
  }

  count -= nvars;
  DELN (count, 2*nvars);

  yals_msg (yals, 1,
    "average literal occurrence %.2f (min %d, max %d)",
    yals_avg (sumoccs, yals->nvars)/2.0, minoccs, maxoccs);

  yals->card_unsat.usequeue = 0; // always a stack!

  // yals_msg (yals, 1,
  //   "using %s for unsat clauses",
  //   yals->unsat.usequeue ? "queue" : "stack");

  // if (yals->card_unsat.usequeue) NEWN (yals->lnk, nclauses);
  // else {
    NEWN (yals->card_pos, yals->card_nclauses);
    for (cidx = 0; cidx < yals->card_nclauses; cidx++) yals->card_pos[cidx] = -1;
    if (yals->using_maxs_weights) {
      NEWN (yals->card_pos_soft, nclauses);
      for (cidx = 0; cidx < yals->card_nclauses; cidx++) yals->card_pos_soft[cidx] = -1;
    }
  // }

  // yals->nvarwords = (nvars + BITS_PER_WORD - 1) / BITS_PER_WORD;

  // yals_msg (yals, 1, "%d x %d-bit words per assignment (%d bytes = %d KB)",
  //   yals->nvarwords,
  //   BITS_PER_WORD,
  //   yals->nvarwords * sizeof (Word),
  //   (yals->nvarwords * sizeof (Word) >> 10));

  // NEWN (yals->set, yals->nvarwords);
  // NEWN (yals->clear, yals->nvarwords);
  // memset (yals->clear, 0xff, yals->nvarwords * sizeof (Word));
  // while (!EMPTY (yals->trail)) {
  //   lit = POP (yals->trail);
  //   idx = ABS (lit);
  //   if (lit < 0) CLRBIT (yals->clear, yals->nvarwords, idx);
  //   else SETBIT (yals->set, yals->nvarwords, idx);
  // }
  // RELEASE (yals->trail);

  // NEWN (yals->vals, yals->nvarwords);
  // NEWN (yals->best, yals->nvarwords);
  // NEWN (yals->tmp, yals->nvarwords);
  // NEWN (yals->flips, nvars);

  if (maxlen < (1<<8)) {
    yals->card_satcntbytes = 1;
    NEWN (yals->card_satcnt1, yals->card_nclauses);
  } else if (maxlen < (1<<16)) {
    yals->card_satcntbytes = 2;
    NEWN (yals->card_satcnt2, yals->card_nclauses);
  } else {
    yals->card_satcntbytes = 4;
    NEWN (yals->card_satcnt4, yals->card_nclauses);
  }
  yals_msg (yals, 1,
    "need %d bytes per cardinality constraint for counting satisfied literals",
    yals->card_satcntbytes);

  // if (yals->opts.crit.val) {

    // always use critical
    // yals_msg (yals, 1,
    //   "dynamically computing break values on-the-fly "
    //   "using critical literals");
    // NEWN (yals->card_crit, yals->card_nclauses);
    // for (cidx = 0; cidx < yals->nclauses; cidx++) {
    //   bound = yals_card_bound (yals, cidx);
    //   NEWN (yals->card_crit[cidx], bound);
    //   while (bound) yals->card_crit[cidx][--bound] = 0;
    // }
    // NEWN (yals->weightedbreak, 2*nvars);
  // } else
  //   yals_msg (yals, 1, "eagerly computing break values");

  // yals_init_weight_to_score_table (yals);

}



/*------------------------------------------------------------------------*/

#define SETOPT(NAME,DEFAULT,MIN,MAX,DESCRIPTION) \
do { \
  int OLD; \
  if (strcmp (name, #NAME)) break; \
  if(val < (MIN)) { \
    yals_warn (yals, \
      "can not set option '%s' smaller than %d", name, (MIN)); \
    val = (MIN); \
  } \
  if(val > (MAX)) { \
    yals_warn (yals, \
      "can not set option '%s' larger than %d", name, (MAX)); \
    val = (MAX); \
  } \
  OLD = yals->opts.NAME.val; \
  if (OLD == val) \
    yals_msg (yals, 2, \
      "keeping option '%s' add old value %d", name, val); \
  else { \
    yals_msg (yals, 1, \
      "setting option '%s' to %d (previous value %d)", name, val, OLD); \
    yals->opts.NAME.val = val; \
  } \
  return 1; \
} while (0)

#undef OPT
#define OPT SETOPT

int yals_setopt (Yals * yals, const char * name, int val) {
  OPTSTEMPLATE
  return 0;
}

/*------------------------------------------------------------------------*/

#define GETOPT(NAME,DEFAULT,MIN,MAX,DESCRIPTION) \
do { \
  if (!strcmp (name, #NAME)) return yals->opts.NAME.val; \
} while (0)

#undef OPT
#define OPT GETOPT

int yals_getopt (Yals * yals, const char * name) {
  OPTSTEMPLATE
  return 0;
}

/*------------------------------------------------------------------------*/

#define USGOPT(NAME,DEFAULT,MIN,MAX,DESCRIPTION) \
do { \
  char BUFFER[120]; int I; \
  sprintf (BUFFER, "--%s=%d..%d", #NAME, (MIN), (MAX)); \
  fputs (BUFFER, yals->out); \
  for (I = 28 - strlen (BUFFER); I > 0; I--) fputc (' ', yals->out); \
  fprintf (yals->out, "%s [%d]\n", (DESCRIPTION), (int)(DEFAULT)); \
} while (0)

#undef OPT
#define OPT USGOPT

void yals_usage (Yals * yals) {
  yals_msglock (yals);
  OPTSTEMPLATE
  yals_msgunlock (yals);
}

/*------------------------------------------------------------------------*/

#define SHOWOPT(NAME,DEFAULT,MIN,MAX,DESCRIPTION) \
do { \
  yals_msg (yals, 0, "--%s=%d", #NAME, yals->opts.NAME); \
} while (0)

#undef OPT
#define OPT SHOWOPT

void yals_showopts (Yals * yals) { OPTSTEMPLATE }

/*------------------------------------------------------------------------*/

static void yals_envopt (Yals * yals, const char * name, Opt * opt) {
  int len = strlen (name) + strlen ("YALS") + 1, val, ch;
  char * env = yals_malloc (yals, len), * p;
  const char * str;
  sprintf (env, "yals%s",name);
  for (p = env; (ch = *p); p++) *p = toupper (ch);
  if ((str = getenv (env))) {
    val = atoi (str);
    val = MIN (opt->min, val);
    val = MAX (opt->max, val);
    opt->val = val;
  }
  yals_free (yals, env, len);
}

#define INITOPT(NAME,DEFAULT,MIN,MAX,DESCRIPTION) \
do { \
  assert ((MIN) <= (DEFAULT)); \
  assert ((DEFAULT) <= (MAX)); \
  yals->opts.NAME.def = (DEFAULT); \
  yals->opts.NAME.val = (DEFAULT); \
  yals->opts.NAME.min = (MIN); \
  yals->opts.NAME.max = (MAX); \
  yals_envopt (yals, #NAME, &yals->opts.NAME); \
} while (0)

#undef OPT
#define OPT INITOPT

static void yals_initopts (Yals * yals) { OPTSTEMPLATE }

/*------------------------------------------------------------------------*/

static void * yals_default_malloc (void * state, size_t bytes) {
  (void) state;
  return malloc (bytes);
}

static void * yals_default_realloc (void * state, void * ptr,
                                    size_t old_bytes, size_t new_bytes) {
  (void) state;
  (void) old_bytes;
  return realloc (ptr, new_bytes);
}

static void yals_default_free (void * state, void * ptr, size_t bytes) {
  (void) state;
  (void) bytes;
  return free (ptr);
}

/*------------------------------------------------------------------------*/

Yals * yals_new_with_mem_mgr (void * mgr,
                              YalsMalloc m, YalsRealloc r, YalsFree f) {
  Yals * yals;
  assert (m), assert (r), assert (f);
  yals = m (mgr, sizeof *yals);
  if (!yals) yals_abort (0, "out-of-memory allocating manager in 'yals_new'");
  memset (yals, 0, sizeof *yals);
  yals->out = stdout;
  yals->mem.mgr = mgr;
  yals->mem.malloc = m;
  yals->mem.realloc = r;
  yals->mem.free = f;
  yals->stats.tmp = INT_MAX;
  yals->stats.best = INT_MAX;
  yals->stats.last = INT_MAX;
  yals->limits.report.min = INT_MAX;

  yals->stats.nheap_updated = 0;

  yals->stats.maxs_best_hard_cnt = INT_MAX;
  yals->stats.maxs_best_soft_cnt = INT_MAX;
  yals->stats.maxs_best_cost = YALS_DOUBLE_MAX;
  yals->stats.maxs_tmp_weight = YALS_DOUBLE_MAX;
  yals->stats.maxs_worst_cost = -1;
  yals->stats.maxs_last = YALS_DOUBLE_MAX;

  yals->stats.maxs_time.weight_transfer = 0;
  yals->stats.maxs_time.break_time = 0;
  yals->stats.maxs_time.make_time = 0;
  yals->stats.maxs_time.initialization = 0;
  yals->stats.maxs_time.var_selection = 0;
  yals->stats.maxs_time.soft_var_selection = 0;
  yals->stats.maxs_time.hard_var_selection = 0;

  yals_inc_allocated (yals, sizeof *yals);
  yals_srand (yals, 0);
  yals_initopts (yals);
  yals->opts.prefix = yals_strdup (yals, YALS_DEFAULT_PREFIX);
  yals->limits.flips = -1;
#ifndef NYALSMEMS
  yals->limits.mems = -1;
#endif
#ifndef NYALSTATS
  yals->stats.wb.min = UINT_MAX;
  yals->stats.wb.max = 0;
#endif
#if 0
  if (getenv ("YALSAMPLES") && getenv ("YALSMOD")) {
    int s = atoi (getenv ("YALSAMPLES")), i;
    int m = atoi (getenv ("YALSMOD"));
    double start = yals_time (yals), delta;
    int64_t * count;
    if (m <= 0) m = 1;
    yals_msg (yals, 0, "starting to sample %d times RNG mod %d", s, m);
    NEWN (count, m);
    for (i = 0; i < s; i++) {
      int r = yals_rand_mod (yals, m);
      assert (0 <= r), assert (r < m);
      count[r]++;
    }
    for (i = 0; i < m; i++)
      yals_msg (yals, 0,
        " mod %6d hit %10d times %7.2f%% with error %7.2f%%",
i, count[i], yals_pct (count[i], s),
        yals_pct (count[i] - s/(double)m, s/(double) m));
    DELN (count, m);
    delta = yals_time (yals) - start;
    yals_msg (yals, 0,
      "finished sampling RNG in %.3f seconds, %.2f ns per 'rand'",
      delta, yals_avg (delta*1e9, s));
  }
#endif
  return yals;
}

Yals * yals_new () {
  return yals_new_with_mem_mgr (0,
  yals_default_malloc, yals_default_realloc, yals_default_free);
}

static void yals_reset_cache (Yals * yals) {
  int ncache = COUNT (yals->cache);
  Word ** w;
  for (w = yals->cache.start; w < yals->cache.top; w++)
    DELN (*w, yals->nvarwords);
  RELEASE (yals->cache);
  yals->cachesizetarget = 0;
  yals_msg (yals, 1, "reset %d cache lines", ncache);
}

void yals_del (Yals * yals) {
  yals_reset_cache (yals);
  yals_reset_unsat (yals);
  free (yals->curr);
  RELEASE (yals->cdb);
  RELEASE (yals->clause);
  RELEASE (yals->mark);
  RELEASE (yals->mins);
  RELEASE (yals->sigs);
  RELEASE (yals->breaks);
  RELEASE (yals->scores);
  RELEASE (yals->cands);
  RELEASE (yals->trail);
  RELEASE (yals->phases);
  RELEASE (yals->exp.table.two);
  RELEASE (yals->exp.table.cb);
  RELEASE (yals->minlits);
  if (yals->unsat.usequeue) DELN (yals->lnk, yals->nclauses);
  else DELN (yals->pos, yals->nclauses);
  DELN (yals->lits, yals->nclauses);
  if (yals->crit) DELN (yals->crit, yals->nclauses);
  if (yals->weightedbreak) DELN (yals->weightedbreak, 2*yals->nvars);
  if (yals->satcntbytes == 1) DELN (yals->satcnt1, yals->nclauses);
  else if (yals->satcntbytes == 2) DELN (yals->satcnt2, yals->nclauses);
  else DELN (yals->satcnt4, yals->nclauses);
  if (yals->weights) DELN (yals->weights, MAXLEN + 1);
  DELN (yals->vals, yals->nvarwords);
  DELN (yals->best, yals->nvarwords);
  DELN (yals->tmp, yals->nvarwords);
  DELN (yals->clear, yals->nvarwords);
  DELN (yals->set, yals->nvarwords);
  DELN (yals->occs, yals->noccs);
  if (yals->refs) DELN (yals->refs, 2*yals->nvars);
  if (yals->flips) DELN (yals->flips, yals->nvars);
#ifndef NYALSTATS
  DELN (yals->stats.inc, yals->stats.nincdec);
  DELN (yals->stats.dec, yals->stats.nincdec);
#endif

  RELEASE (yals->clause_size); // missing from original....
  // cardinality structures
  RELEASE (yals->card_cdb);
  RELEASE (yals->card_size);
  DELN (yals->card_pos, yals->card_nclauses);
  if (yals->card_refs) DELN (yals->card_refs, 2*yals->nvars);
  DELN (yals->card_lits, yals->card_nclauses);
  DELN (yals->card_occs, yals->card_noccs);
  if (yals->card_satcntbytes == 1) DELN (yals->card_satcnt1, yals->card_nclauses);
  else if (yals->satcntbytes == 2) DELN (yals->card_satcnt2, yals->card_nclauses);
  else DELN (yals->card_satcnt4, yals->card_nclauses);



  RELEASE (yals->lit_scores);

  //maxs
  RELEASE (yals->maxs_clause_weights);
  RELEASE (yals->maxs_card_weights);
  DELN (yals->hard_clause_ids, yals->nclauses);
  DELN (yals->hard_card_ids, yals->card_nclauses);
  // more to be deledted that is untracked

  if (yals->using_maxs_weights) {
    DELN (yals->pos_soft, yals->nclauses);
    DELN (yals->card_pos_soft, yals->card_nclauses);
    RELEASE (yals->ddfw.uvars_heap_soft.stack);

    DELN (yals->ddfw.uvars_heap_soft.pos, yals->nvars);
    DELN (yals->ddfw.uvars_heap_soft.score, yals->nvars);
  }

  //ddfw
  RELEASE (yals->ddfw.satisfied_clauses);
  RELEASE (yals->ddfw.helper_hash_changed_idx);
  RELEASE (yals->ddfw.helper_hash_changed_idx1);
  RELEASE (yals->ddfw.sat_clauses);
  RELEASE (yals->ddfw.uvars);
  RELEASE (yals->ddfw.uvars_soft);
  RELEASE (yals->ddfw.card_helper_hash_changed_idx);
  RELEASE (yals->ddfw.uvars_changed);

  RELEASE (yals->ddfw.uvars_heap.stack);
  DELN (yals->ddfw.uvars_heap.pos, yals->nvars);
  DELN (yals->ddfw.uvars_heap.score, yals->nvars);

  // ddfw data structures allocated using malloc/calloc
  yals_nbr_free (yals);
  free (yals->ddfw.cc_comp);
  free (yals->ddfw.max_weighted_neighbour);
  free (yals->ddfw.sat_count_in_clause);
  free (yals->ddfw.helper_hash_clauses);
  free (yals->ddfw.helper_hash_vars);
  free (yals->ddfw.ddfw_clause_weights);
  free (yals->ddfw.unsat_weights);
  free (yals->ddfw.sat1_weights);
  free (yals->ddfw.uwrvs);
  free (yals->ddfw.uwvars_gains);
  free (yals->ddfw.non_increasing);
  free (yals->ddfw.uvar_pos);
  free (yals->ddfw.uvar_changed_pos);
  free (yals->ddfw.var_unsat_count );
  free (yals->ddfw.uvar_pos_soft);
  free (yals->ddfw.var_unsat_count_soft);
  free (yals->ddfw.card_sat_count_in_clause);
  free (yals->ddfw.card_helper_hash_clauses);
  free (yals->ddfw.ddfw_card_weights );
  free (yals->ddfw.unsat_weights_soft );
  free (yals->ddfw.sat1_weights_soft);


  yals_strdel (yals, yals->opts.prefix);
  yals_dec_allocated (yals, sizeof *yals);
  // yals_msg (yals, 1, "allocated %d",yals->stats.allocated.current);
  assert (getenv ("YALSLEAK") || !yals->stats.allocated.current);
  yals->mem.free (yals->mem.mgr, yals, sizeof *yals);
}

void yals_setprefix (Yals * yals, const char * prefix) {
  yals_strdel (yals, yals->opts.prefix);
  yals->opts.prefix = yals_strdup (yals, prefix ? prefix : "");
}

void yals_setout (Yals * yals, FILE * out) {
  yals->out = out;
}

void yals_setphase (Yals * yals, int lit) {
  if (!lit) yals_abort (yals, "zero literal argument to 'yals_val'");
  PUSH (yals->phases, lit);
}

void yals_setflipslimit (Yals * yals, long long flips) {
  yals->limits.flips = flips;
  yals_msg (yals, 1, "new flips limit %lld", (long long) flips);
}

void yals_setmemslimit (Yals * yals, long long mems) {
#ifndef NYALSMEMS
  yals->limits.mems = mems;
  yals_msg (yals, 1, "new mems limit %lld", (long long) mems);
#else
  yals_warn (yals,
    "can not set mems limit to %lld "
    "(compiled without 'mems' support)",
    (long long) mems);
#endif
}

/*------------------------------------------------------------------------*/

void yals_setime (Yals * yals, double (*time)(void)) {
  yals->cbs.time = time;
}

void yals_seterm (Yals * yals, int (*term)(void *), void * state) {
  yals->cbs.term.state = state;
  yals->cbs.term.fun = term;
}

void yals_setmsglock (Yals * yals,
                      void (*lock)(void *),
                      void (*unlock)(void *),
     void * state) {
  yals->cbs.msg.state = state;
  yals->cbs.msg.lock = lock;
  yals->cbs.msg.unlock = unlock;
}

/*------------------------------------------------------------------------*/

static void yals_new_clause (Yals * yals) {
  int len = COUNT (yals->clause), * p, lit;
  if (!len) {
    LOG ("found empty clause in original formula");
    yals->mt = 1;
  }
  if (len == 1) {
    // soft units are not assigned
    if (yals->using_maxs_weights) {
      if (yals->parsed_weight != yals->maxs_hard_weight)
        LOG("found soft unit %d",PEEK (yals->clause, 0));
      else 
        PUSH (yals->trail, PEEK (yals->clause, 0));
    } else {
      lit = PEEK (yals->clause, 0);
      LOG ("found unit clause %d in original formula", lit);
      PUSH (yals->trail, lit);
      }
  }
  for (p = yals->clause.start; p < yals->clause.top; p++) {
    lit = *p;
    PUSH (yals->cdb, lit);
  }
  PUSH (yals->cdb, 0);
  LOGLITS (yals->cdb.top - len - 1, "new length %d", len);
  if (yals->using_maxs_weights) {
      PUSH (yals->maxs_clause_weights, yals->parsed_weight);
      if (yals->parsed_weight != yals->maxs_hard_weight)
        yals->maxs_acc_hard_weight += yals->parsed_weight;
    }
}

void yals_clause_add_weight (Yals * yals, double weight) {
  assert (weight >= 0);
  yals->parsed_weight = weight;
}

static signed char yals_sign (int lit) { return (lit < 0) ? -1 : 1; }

void yals_add (Yals * yals, int lit) {
  if (lit) {
    signed char mark;
    int idx;
    if (lit == INT_MIN)
      yals_abort (yals, "can not add 'INT_MIN' as literal");
    idx = ABS (lit);
    if (idx == INT_MAX)
      yals_abort (yals, "can not add 'INT_MAX' as literal");
    if (idx >= yals->nvars) yals->nvars = idx + 1;
    while (idx >= COUNT (yals->mark)) PUSH (yals->mark, 0);
    mark = PEEK (yals->mark, idx);
    if (lit < 0) mark = -mark;
    if (mark < 0) yals->trivial = 1;
    else if (!mark) {
      PUSH (yals->clause, lit);
      POKE (yals->mark, idx, yals_sign (lit));
    }

    // check if formula is pure on each lit parsed
    if (yals->using_maxs_weights) {
      int polarity = ABS (lit) / lit;
      if (yals->maxs_hard_weight == yals->parsed_weight) {
        if (yals->hard_polarity == 0) {
          yals->hard_polarity = polarity;
        } else if (yals->hard_polarity != polarity) 
          yals->is_pure = 0;
      } else {
        if (yals->hard_polarity == polarity) 
          yals->is_pure = 0;
      }
    }

  } else {
    const int * p;
    int size = 0;
    for (p = yals->clause.start; p < yals->clause.top; p++)
    {
      POKE (yals->mark, ABS (*p), 0);
      size++;
    }
    PUSH (yals->clause_size, size);

    if (yals->trivial) yals->trivial = 0;
    else yals_new_clause (yals);
    CLEAR (yals->clause);
  }
}

/*------------------------------------------------------------------------*/

#define ISDEFSTRAT(NAME,ENABLED) \
do { \
  if (!(ENABLED)) { \
    assert (yals->strat.NAME == yals->opts.NAME.val); \
    break; \
  } \
  if (yals->strat.NAME != yals->opts.NAME.val) return 0; \
} while (0)
#undef STRAT
#define STRAT ISDEFSTRAT

static int yals_is_default_strategy (Yals * yals) {
  STRATSTEMPLATE
  return 1;
}

#define PRINTSTRAT(NAME,ENABLED) \
do { \
  if (!(ENABLED)) break; \
  fprintf (yals->out, " --%s=%d", #NAME, yals->strat.NAME); \
} while (0)
#undef STRAT
#define STRAT PRINTSTRAT

static void yals_print_strategy (Yals * yals, const char * type, int vl) {
  if (yals->opts.verbose.val < vl) return;
  yals_msglock (yals);
  fprintf (yals->out, "%s%s", yals->opts.prefix, type);
  STRATSTEMPLATE
  if (yals_is_default_strategy (yals)) fprintf (yals->out, " (default)");
  else fprintf (yals->out, " (random)");
  fprintf (yals->out, "\n");
  yals_msgunlock (yals);
}

/*------------------------------------------------------------------------*/

#define DEFSTRAT(NAME,ENABLED) \
do { \
  yals->strat.NAME = yals->opts.NAME.val; \
} while (0)
#undef STRAT
#define STRAT DEFSTRAT

static void yals_set_default_strategy (Yals * yals) {
  STRATSTEMPLATE
  yals->stats.strat.def++;
}

/*------------------------------------------------------------------------*/

static int yals_rand_opt (Yals * yals, Opt * opt, const char * name) {
  unsigned mod, r;
  int res;
  mod = opt->max;
  mod -= opt->min;
  mod++;
  if (mod) {
    r = yals_rand_mod (yals, mod);
    res = (int)(r + (unsigned) opt->min);
  } else {
    assert (opt->min == INT_MIN);
    assert (opt->max == INT_MAX);
    res = (int) yals_rand (yals);
  }
  assert (opt->min <= res), assert (res <= opt->max);
  (void) name;
  LOG ("randomly picking strategy %s=%d from [%d,%d] default %d",
    name, res, opt->min, opt->max, opt->val);
  return res;
}

#define RANDSTRAT(NAME,ENABLED) \
do { \
  if ((ENABLED)) { \
    yals->strat.NAME = \
      yals_rand_opt (yals, &yals->opts.NAME, #NAME); \
  } else yals->strat.NAME = yals->opts.NAME.val; \
} while (0)
#undef STRAT
#define STRAT RANDSTRAT

static void yals_set_random_strategy (Yals * yals) {
  STRATSTEMPLATE
  assert (yals->stats.restart.inner.count > 1);
  yals->stats.strat.rnd++;
  if (yals->strat.cached)
    yals->strat.pol = yals->opts.pol.val;
}

/*------------------------------------------------------------------------*/

static void yals_pick_strategy (Yals * yals) {
  assert (yals->stats.restart.inner.count > 0);
  if (yals->stats.restart.inner.count == 1 ||
      !yals_rand_mod (yals, yals->opts.fixed.val))
    yals_set_default_strategy (yals);
  else yals_set_random_strategy (yals);
  yals_print_strategy (yals, "picked strategy:", 2);
}

static void yals_fix_strategy (Yals * yals) {
  if (yals->uniform) {
    yals->strat.correct = 1;
    yals->strat.pol = 0;
    yals->strat.uni = 1;
    yals->strat.weight = 1;
    yals_print_strategy (yals, "fixed strategy:", 2);
  }
}

/*------------------------------------------------------------------------*/

static int yals_inner_restart_interval (Yals * yals) {
  int res = yals->opts.restart.val;
  if (res < yals->nvars/2) res = yals->nvars/2;
  return res;
}

static int64_t yals_outer_restart_interval (Yals * yals) {
  int64_t res = yals_inner_restart_interval (yals);
  res *= yals->opts.restartouterfactor.val;
  assert (res >= 0);
  return res;
}

static int yals_inc_inner_restart_interval (Yals * yals) {
  int64_t interval;
  int res;

  if (yals->opts.restart.val > 0) {
    if (yals->opts.reluctant.val) {
      if (!yals->limits.restart.inner.rds.u)
yals->limits.restart.inner.rds.u =
 yals->limits.restart.inner.rds.v = 1;
      interval = yals->limits.restart.inner.rds.v;
      interval *= yals_inner_restart_interval (yals);
      yals_rds (&yals->limits.restart.inner.rds);
    } else {
      if (!yals->limits.restart.inner.interval)
yals->limits.restart.inner.interval =
 yals_inner_restart_interval (yals);
      interval = yals->limits.restart.inner.interval;
      if (yals->limits.restart.inner.interval <= YALS_INT64_MAX/2)
yals->limits.restart.inner.interval *= 2;
      else yals->limits.restart.inner.interval = YALS_INT64_MAX;
    }
  } else interval = YALS_INT64_MAX;

  yals_msg (yals, 2, "next restart interval %lld", interval);

  if (YALS_INT64_MAX - yals->stats.flips >= interval)
    yals->limits.restart.inner.lim = yals->stats.flips + interval;
  else
    yals->limits.restart.inner.lim = YALS_INT64_MAX;

  yals_msg (yals, 2,
    "next restart at %lld",
    yals->limits.restart.inner.lim);

  res = (yals->stats.restart.inner.maxint < interval);
  if (res) {
    yals->stats.restart.inner.maxint = interval;
    yals_msg (yals, 2, "new maximal restart interval %lld", interval);
  }
  return res;
}

static int yals_need_to_restart_inner (Yals * yals) {
  if (yals->uniform &&
      yals->stats.restart.inner.count >= yals->opts.unirestarts.val)
    return 0;
  return yals->inner_restart && yals->stats.flips >= yals->limits.restart.inner.lim;
}

static int yals_need_to_restart_outer (Yals * yals) {
  return yals->stats.flips >= yals->limits.restart.outer.lim;
}

void save_current_assignment (Yals *yals)
{
  size_t bytes = yals->nvarwords * sizeof (Word);
  if (yals->curr)
    free (yals->curr);
  yals->curr = malloc (bytes);
  memcpy (yals->curr, yals->vals, bytes);
}

static void yals_restart_inner (Yals * yals) {
  double start;
  // assert (yals_need_to_restart_inner (yals)); // disabled because we are only doing max tries right now
  start = yals_time (yals);
  yals->stats.restart.inner.count++;
  if ((yals_inc_inner_restart_interval (yals) && yals->opts.verbose.val) ||
      yals->opts.verbose.val >= 2) {
      if (yals->using_maxs_weights)
        yals_maxs_report (yals, "restart %lld", yals->stats.restart.inner.count);
      else 
    yals_report (yals, "restart %lld", yals->stats.restart.inner.count);
      }
  
  if (yals->using_maxs_weights) {
    if (yals->stats.maxs_best_cost < yals->stats.maxs_last) {
      yals->stats.pick.keep++;
      yals_msg (yals, 2,
        "keeping strategy and assignment thus essentially skipping restart");
    } else {
      yals_cache_assignment (yals);
      yals_pick_strategy (yals);
      yals_fix_strategy (yals);
      save_current_assignment (yals);
      yals_pick_assignment (yals, 0);
      // If a shared cache is attached (palsat), it may override the
      // per-worker pick with an assignment drawn from the shared pool.
      if (yals_shared_cache_cycle (yals)) {
        yals_remove_trailing_bits (yals);
        yals_set_units (yals);
      }
      yals_update_sat_and_unsat (yals);
      yals->stats.tmp = INT_MAX;
      yals->stats.maxs_tmp_weight = YALS_DOUBLE_MAX;
      yals_save_new_minimum (yals);
    }
  } else {
    if (yals->stats.best < yals->stats.last) {
      yals->stats.pick.keep++;
      yals_msg (yals, 2,
        "keeping strategy and assignment thus essentially skipping restart");
    } else {
      yals_cache_assignment (yals);
      yals_pick_strategy (yals);
      yals_fix_strategy (yals);
      save_current_assignment (yals);
      yals_pick_assignment (yals, 0);
      if (yals_shared_cache_cycle (yals)) {
        yals_remove_trailing_bits (yals);
        yals_set_units (yals);
      }
      yals_update_sat_and_unsat (yals);
      yals->stats.tmp = INT_MAX;
      yals_save_new_minimum (yals);
    }
  }
  yals->stats.last = yals->stats.best;
  yals->stats.maxs_last = yals->stats.maxs_best_cost;
  yals->stats.time.restart += yals_time (yals) - start;
}

/*------------------------------------------------------------------------*/

static int yals_done (Yals * yals) {
  assert (!yals->mt);
  if (!yals_nunsat (yals)) return 1;
  if (yals->limits.flips >= 0 &&
      yals->limits.flips <= yals->stats.flips) {
    yals_msg (yals, 1,
      "flips limit %lld after %lld flips reached",
      yals->limits.flips, yals->stats.flips);
    return -1;
  }
#ifndef NYALSMEMS
  if (yals->limits.mems >= 0 &&
      yals->limits.mems <= yals->stats.mems.all) {
    yals_msg (yals, 1,
      "mems limit %lld after %lld mems reached",
      yals->limits.mems, yals->stats.mems.all);
    return -1;
  }
#endif
  if (yals->cbs.term.fun && yals->limits.term-- <= 0) {
    yals->limits.term = yals->opts.termint.val;
    if (yals->cbs.term.fun (yals->cbs.term.state)) {
      yals_msg (yals, 1, "forced to terminate");
      return -1;
    }
  }
  if (yals->opts.hitlim.val >= 0 &&
      yals->stats.hits  >= yals->opts.hitlim.val) {
    yals_msg (yals, 1,
      "minimum hits limit %lld reached after %lld hits",
      yals->opts.hitlim.val, yals->stats.hits);
    return -1;
  }
  return 0;
}

static void yals_init_inner_restart_interval (Yals * yals) {
  memset (&yals->limits.restart.inner, 0, sizeof yals->limits.restart.inner);
  yals->limits.restart.inner.lim = yals->stats.flips;
  yals->stats.restart.inner.maxint = 0;
}




/*

  Transfered w constraint weight from source to sink.

  Need to update the critical and unsat literals from both constraints to 
  account fo the change in weight.

*/
void yals_ddfw_update_lit_weights_on_weight_transfer (Yals *yals, int sink, int source, int constraint_type_source, int constraint_type_sink, double w)
{
  double maxs_weight = 1.0;
  int soft = 0;
  // if source is critical, 
  //   pulling weight from critical literals
  if (constraint_type_source == TYPECLAUSE) {
    if (yals->using_maxs_weights && !yals->hard_clause_ids[source]) {
      soft = 1;
      if (!yals->opts.maxs_init_weight_relative.val)
        maxs_weight = PEEK (yals->maxs_clause_weights, source);
    }

    if (yals_satcnt (yals, source) == 1) // also pulling this transferred weight off critical lit list
      // sat1_weights [get_pos(yals->crit [source])] -= w * maxs_weight;
      yals_ddfw_update_var_weight (yals, yals->crit [source], soft, 1, -w * maxs_weight);
  } else if (constraint_type_source == TYPECARDINALITY) { // ASSUME Cardinality constraints are soft
    if (yals_card_satcnt (yals, source) <= yals_card_bound (yals, source)) {
      // critical cardinality constraint when falsified
      // get change in critical values
      double old_weight = yals->ddfw.ddfw_card_weights [source] + w;
      // double new_weight = yals->ddfw.ddfw_card_weights [source];

      // double old_unsat_weight = yals->ddfw.card_clause_calculated_weights[source];
      double old_unsat_weight = yals_card_calculate_weight (yals, yals_card_bound (yals, source), yals_card_satcnt (yals, source), old_weight, source);
      double new_unsat_weight = yals_card_get_calculated_weight (yals, source);

      double w_next = yals_card_calculate_weight (yals, yals_card_bound (yals, source), yals_card_satcnt (yals, source)-1, old_weight, source);
      double old_critical = w_next - old_unsat_weight;
      double new_critical = yals_card_get_calculated_weight_change_neg (yals, source);

      yals_card_sat_weight_update (yals, source, new_critical - old_critical, 0);

      if (yals_card_satcnt (yals, source) < yals_card_bound (yals, source)) {
        // falsified constraint, need to update unsat literals as well
        yals_card_unsat_weight_update (yals, source, new_unsat_weight - old_unsat_weight, 0);
      }

      // yals->ddfw.card_clause_calculated_weights[source] = new_unsat_weight;
    }
    
  }

  
  maxs_weight = 1.0;
  // adding weight to unsat literals from sink
  if (constraint_type_sink == TYPECLAUSE) {
    int * lits = yals_lits (yals, sink), lit;
    if (yals->using_maxs_weights && !yals->hard_clause_ids[sink]) {
      soft = 1;
      if (!yals->opts.maxs_init_weight_relative.val)
        maxs_weight = PEEK (yals->maxs_clause_weights, sink);
    }

    while ((lit = *lits++))
      // unsat_weights [get_pos(lit)] += w *  maxs_weight;
      yals_ddfw_update_var_weight (yals, lit, soft, 0, w *  maxs_weight);
  } else if (constraint_type_sink == TYPECARDINALITY) {
    // critical cardinality constraint when falsified
    // get change in critical values
    double old_weight = yals->ddfw.ddfw_card_weights [sink] - w; // difference, now gaining weight
    // double new_weight = yals->ddfw.ddfw_card_weights [sink];

    // double old_unsat_weight = yals->ddfw.card_clause_calculated_weights[sink];
    double old_unsat_weight = yals_card_calculate_weight (yals, yals_card_bound (yals, sink), yals_card_satcnt (yals, sink), old_weight, sink);
    double new_unsat_weight = yals_card_get_calculated_weight (yals, sink);

    double w_next = yals_card_calculate_weight (yals, yals_card_bound (yals, sink), yals_card_satcnt (yals, sink)-1, old_weight, sink);
    double old_critical = w_next - old_unsat_weight;
    double new_critical = yals_card_get_calculated_weight_change_neg (yals, sink);

    yals_card_sat_weight_update (yals, sink, new_critical - old_critical, 0);

    if (yals_card_satcnt (yals, sink) < yals_card_bound (yals, sink)) {
      // falsified constraint, need to update unsat literals as well
      yals_card_unsat_weight_update (yals, sink, new_unsat_weight - old_unsat_weight, 0);
    }

    // yals->ddfw.card_clause_calculated_weights[sink] = new_unsat_weight;
    LOGCARDCIDX (sink, "from %lf to %lf weight",old_unsat_weight, new_unsat_weight);
  }
}

// if actually using this, store the length in an array
double compute_degree_of_satisfaction (Yals *yals, int cidx)
{
  int len = 0, lit;
  int * lits = yals_lits (yals, cidx);
  while ((lit=*lits++)) len++; 
  double ds = (double) yals_satcnt (yals, cidx) / (double) len; 
  return ds;
}

double linear_wt (Yals * yals, int source, int type_source)
{
  double source_weight = 0.0;

  if (type_source == TYPECLAUSE) {
    source_weight = yals->ddfw.ddfw_clause_weights [source];
  } else if (type_source == TYPECARDINALITY) {
    source_weight = yals->ddfw.ddfw_card_weights [source];
  }

  // weight transfer: w = source_weight^p + a*source_weight + c
  double p = (float) yals->opts.wtpow.val / 1000.0;
  double a = (float) yals->opts.wtmul.val / 1000.0;
  double c = (float) yals->opts.wtadd.val / 1000.0;
  return (double) (pow ((float) source_weight, (float) p)
                   + (float) source_weight * (float) a + (float) c);
}

/*
  Given a constraint (either clause or cardinality),
  find neighboring sat clause/constraint with largest weight.
  Weight must be larger than initial weight. 
  If relative, initial weight for soft constraints is 
  MaxSAT weight.

  Could return max weighted, even if not greater than initial weight
  (option ignorewtcriteria=1)

  Could return -1 if no source for weight transfer was found.

  Functionality:
    Look at neighbors, 
      constraints with the same literal same polarity.

    If neighborsplus=1 and no source found in neighbors,
    Look at neighbors+,
      constraints with same literal different polarity.

    Note, if the constraint type is a cardinality constraint, 
    some of the literals within the constraint may be true 
    even if the constraint is falsified. We must check for this
    and ensure we are not viewing neighbors with those literals,
    and that neighbors+ with those literals are overly satsified. 

  idea: Could return both the clause and cardinality constraint then coin flip which to trade from

  idae: Could randomly select among those with the same max weight so you don't
    always end up with constraints from similar neighborhoods depending on literal
    order within the constraint.
*/
int yals_ddfw_get_max_weight_sat_clause (Yals *yals, int cidx, int constraint_type, int* return_con_type) {
  int * lits = NULL, lit;
  int occ, nidx;
  double best_w;
  int * occs, *p;
  int source = -1;
  LOG ("get max sat for %d", cidx);
  int takes_hard, takes_soft;
  int source_hard = 0;

  takes_hard = takes_soft = 1;

  double best_cls_wt, best_card_wt;
  best_cls_wt = best_card_wt = best_w = 0.0;
  // Tie-break: among equal-weight eligible neighbors prefer the smallest
  // unified id (clause u, or nclauses+card). Shared by the scan and the heap
  // so both pick the same source -> identical search path with/without litheap.
  int best_uid = INT_MAX;

  // soft constraints are using their MaxSAT weights as DDFW weights
  int relative = (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights);

  // check if source can be hard or soft
  //  we are only applying this to random transfer now
  //  everything can take from everything in this function
  // if (!yals->current_weight_transfer_soft && !yals->opts.maxs_hard_takes_soft.val)
  //   takes_soft = 0;
  // if (yals->current_weight_transfer_soft && !yals->opts.maxs_soft_takes_hard.val)
  //   takes_hard = 0;


  // get lits from the input constraint
  if (constraint_type == TYPECLAUSE) {
    lits = yals_lits (yals, cidx);
  } else if (constraint_type == TYPECARDINALITY) {
    lits = yals_card_lits (yals, cidx);
  } else {yals_abort (yals, "incorrect constraint type");}

  // --rndlit: instead of scanning the neighbors of every falsified literal of
  // the sink, pick one falsified literal uniformly at random and only scan its
  // neighbors. rndlit_target is the index (among falsified lits) to process.
  int rndlit_target = -1, rndlit_seen = -1;
  if (yals->opts.rndlit.val) {
    int nfalse = 0, * rp = lits, rl;
    while ((rl = *rp++)) if (!yals_val (yals, rl)) nfalse++;
    if (!nfalse) return -1;
    rndlit_target = yals_rand_mod (yals, nfalse);
  }

  // loop over neighbors
  //   constraints with same literal same polarity
  while ((lit=*lits++))
  {
    // skip satisfied lits from cardinality constraints
    //   (could technically get an iterator over only falsified 
    //   lits since the cardinality constraints are sorted,
    //   don't this would save much time unless constraints
    //   were huge)
    if (yals_val (yals, lit)) continue;
    // rndlit: skip every falsified literal except the randomly chosen one
    if (rndlit_target >= 0 && ++rndlit_seen != rndlit_target) continue;

    if (yals->opts.litheap.val) {
      // --litheap: peek this literal's heaviest eligible neighbor via its
      // max-heap (+ lazy skip) instead of scanning all of its occurrences.
      int nbr_ct, cand = yals_nbr_best (yals, lit, &nbr_ct);
      if (cand >= 0) {
        double cw = (nbr_ct == TYPECLAUSE)
          ? yals->ddfw.ddfw_clause_weights [cand]
          : yals->ddfw.ddfw_card_weights [cand];
        int cuid = (nbr_ct == TYPECLAUSE) ? cand : yals->nclauses + cand;
        if (cw > best_w || (cw == best_w && cuid < best_uid)) {
          source = cand; best_w = cw; best_uid = cuid; *return_con_type = nbr_ct;
        }
      }
    } else {

    // neighbor clauses
    occs = yals_occs (yals, lit);
    for (p = occs; (occ = *p) >= 0; p++) {
      nidx = occ >> LENSHIFT;
      LOG ("CHECKING %d with weight %lf", nidx, yals->ddfw.ddfw_clause_weights [nidx]);

      source_hard = yals->hard_clause_ids [nidx];
      if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

      if (yals_satcnt (yals, nidx)>0) { // clause is satisfied
        // check if clause has geq it's initial weight, then (weight, id) tie-break
        double thr = (relative && !source_hard) ? PEEK (yals->maxs_clause_weights, nidx)
                                                 : (double) yals->opts.init_clause_weight.val;
        if (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_clause_weights [nidx] >= thr) {
          double cw = yals->ddfw.ddfw_clause_weights [nidx];
          if (cw > best_w || (cw == best_w && nidx < best_uid)) {
            source = nidx; best_w = cw; best_uid = nidx; *return_con_type = TYPECLAUSE;
          }
        }
      }
    }
    // neighbor cardinality constraints
    occs = yals_card_occs (yals, lit);
    for (p = occs; (occ = *p) >= 0; p++) {
      nidx = occ >> LENSHIFT;
      LOG ("CHECKING card %d with weight %lf", nidx, yals->ddfw.ddfw_clause_weights [nidx]);

      source_hard = yals->hard_card_ids [nidx];
      if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

      if (yals_card_satcnt (yals, nidx)>= yals_card_bound (yals, nidx)) { // constraint satisfied
        // check if cardinality constraint has geq it's initial weight, then (weight, id) tie-break
        double thr = (relative && !source_hard) ? PEEK (yals->maxs_card_weights, nidx)
                                                 : (double) yals->opts.init_card_weight.val;
        if (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_card_weights [nidx] >= thr) {
          double cw = yals->ddfw.ddfw_card_weights [nidx];
          int cuid = yals->nclauses + nidx;
          if (cw > best_w || (cw == best_w && cuid < best_uid)) {
            source = nidx; best_w = cw; best_uid = cuid; *return_con_type = TYPECARDINALITY;
          }
        }
      }
    }
    } // end --litheap else (occurrence-scan path)
    // rndlit: only the one chosen literal's neighbors are examined
    if (rndlit_target >= 0) break;
  }

  best_w = 0.0; // reset best weight for pass of neighbors+

  // if no source found,
  // loop over neighbors+
  //   constraints with same literal different polarity
  if (yals->opts.neighbors_plus.val && source == -1 && (!yals->is_pure || (takes_hard && takes_soft))) {
    // if pure, this implies we are taking from the other type of constaint (soft vs hard)
    // can skip this loop if we have this disabled in the options

    if (constraint_type == TYPECLAUSE) {
      lits = yals_lits (yals, cidx);
    } else if (constraint_type == TYPECARDINALITY) {
      lits = yals_card_lits (yals, cidx);
    } else {yals_abort (yals, "incorrect constraint type");}

    // First loop through lits that are true.
    // Since they are true within the cardinality constraint,
    // we will not need to flip them.
    while ((lit=*lits++)) {
      if (!yals_val (yals, lit)) continue; 

      // neighbors+ clauses
      occs = yals_occs (yals, -lit);
      for (p = occs; (occ = *p) >= 0; p++) 
      {
        nidx = occ >> LENSHIFT;
        LOG ("CHECKING %d with weight %lf", nidx, yals->ddfw.ddfw_clause_weights [nidx]);

        source_hard = yals->hard_clause_ids [nidx];
        if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

        if (yals_satcnt (yals, nidx)>= 1) {
          if (relative && !source_hard) {
            if ( (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_clause_weights [nidx] >= PEEK (yals->maxs_clause_weights, nidx))  && yals->ddfw.ddfw_clause_weights [nidx] >= best_w) {
              source = nidx;
              best_w = yals->ddfw.ddfw_clause_weights [nidx];
              *return_con_type = TYPECLAUSE;
            }
          } else {
            if ( (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_clause_weights [nidx] >= yals->opts.init_clause_weight.val) && yals->ddfw.ddfw_clause_weights [nidx] >= best_w) {
              source = nidx;
              best_w = yals->ddfw.ddfw_clause_weights [nidx];
              *return_con_type = TYPECLAUSE;
            }
          }
        }
      }
      // neighbors+ cardinality constraints
      occs = yals_card_occs (yals, -lit);
      for (p = occs; (occ = *p) >= 0; p++) {
        nidx = occ >> LENSHIFT;
        LOG ("CHECKING card %d with weight %lf", nidx, yals->ddfw.ddfw_clause_weights [nidx]);

        source_hard = yals->hard_card_ids [nidx];
        if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

        if (yals_card_satcnt (yals, nidx)>= yals_card_bound (yals, nidx)) { // constraint satisfied
          // check if cardinality constraint has geq it's initial weight
          if (relative && !source_hard) {
            if ( (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_card_weights [nidx] >= PEEK (yals->maxs_card_weights, nidx))  && yals->ddfw.ddfw_card_weights [nidx] >= best_w) {
                source = nidx;
                best_w = yals->ddfw.ddfw_card_weights [nidx];
                *return_con_type = TYPECARDINALITY;
              }
          } else {
            if ((yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_card_weights [nidx] >= yals->opts.init_card_weight.val) && yals->ddfw.ddfw_card_weights [nidx] >= best_w) {
              source = nidx;
              best_w = yals->ddfw.ddfw_card_weights [nidx];
              *return_con_type = TYPECARDINALITY;
            }
          }
        }
      }
    }
  }
  

  // Second loop through lits that are false.
  // Since they are false within the cardinality constraint, 
  // we will need to flip them, and therefore we look at 
  // overly satsified neighbors.
  // Idea: do this loop before the first one.
  if (yals->opts.neighbors_plus.val && source == -1 && (!yals->is_pure || (!takes_hard && !takes_soft))) {

    if (constraint_type == TYPECLAUSE) {
      lits = yals_lits (yals, cidx);
    } else if (constraint_type == TYPECARDINALITY) {
      lits = yals_card_lits (yals, cidx);
    } else {yals_abort (yals, "incorrect constraint type");}

    while ((lit=*lits++)) {
      if (!yals_val (yals, lit)) continue; 

      // neighbors+ clauses
      occs = yals_occs (yals, -lit);
      for (p = occs; (occ = *p) >= 0; p++) 
      {
        nidx = occ >> LENSHIFT;
        LOG ("CHECKING %d with weight %lf", nidx, yals->ddfw.ddfw_clause_weights [nidx]);

        source_hard = yals->hard_clause_ids [nidx];
        if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

        if (yals_satcnt (yals, nidx)> 1) { // clause overly! satisifed
          if (relative && !source_hard) {
            if ( (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_clause_weights [nidx] >= PEEK (yals->maxs_clause_weights, nidx))  && yals->ddfw.ddfw_clause_weights [nidx] >= best_w) {
              source = nidx;
              best_w = yals->ddfw.ddfw_clause_weights [nidx];
              *return_con_type = TYPECLAUSE;
            }
          } else {
            if ( (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_clause_weights [nidx] >= yals->opts.init_clause_weight.val) && yals->ddfw.ddfw_clause_weights [nidx] >= best_w) {
              source = nidx;
              best_w = yals->ddfw.ddfw_clause_weights [nidx];
              *return_con_type = TYPECLAUSE;
            }
          }
        }
      }
      // neighbors+ cardinality constraints
      occs = yals_card_occs (yals, -lit);
      for (p = occs; (occ = *p) >= 0; p++) {
        nidx = occ >> LENSHIFT;
        LOG ("CHECKING card %d with weight %lf", nidx, yals->ddfw.ddfw_clause_weights [nidx]);

        source_hard = yals->hard_card_ids [nidx];
        if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

        if (yals_card_satcnt (yals, nidx)> yals_card_bound (yals, nidx)) { // constraint overly! satisfied
          // check if cardinality constraint has geq it's initial weight
          if (relative && !source_hard) {
            if ( (yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_card_weights [nidx] >= PEEK (yals->maxs_card_weights, nidx))  && yals->ddfw.ddfw_card_weights [nidx] >= best_w) {
                source = nidx;
                best_w = yals->ddfw.ddfw_card_weights [nidx];
                *return_con_type = TYPECARDINALITY;
              }
          } else {
            if ((yals->opts.ignorewtcriteria.val || yals->ddfw.ddfw_card_weights [nidx] >= yals->opts.init_card_weight.val) && yals->ddfw.ddfw_card_weights [nidx] >= best_w) {
              source = nidx;
              best_w = yals->ddfw.ddfw_card_weights [nidx];
              *return_con_type = TYPECARDINALITY;
            }
          }
        }
      }
    }
  }

  // source for weight transfer
  // may be (-1), i.e., no source found
  return source;
}

/*------------------------------------------------------------------------*/
/* Connected components by shared-literal connectivity (componentlock).    */
/* Two constraints are connected if they share a common (signed) literal.  */
/* Weight transfer is restricted to within a component when enabled.       */
/* Note: positive-only and negative-only constraints never share a literal */
/* (+x != -x), so they always land in different components -> no pos<->neg */
/* weight transfer, which is the motivating use case.                      */
/*------------------------------------------------------------------------*/

static int yals_cc_find (int * parent, int x) {
  while (parent[x] != x) { parent[x] = parent[parent[x]]; x = parent[x]; }
  return x;
}
static void yals_cc_union (int * parent, int a, int b) {
  int ra = yals_cc_find (parent, a), rb = yals_cc_find (parent, b);
  if (ra != rb) parent[ra] = rb;
}

// Unified constraint id: clause cidx -> cidx; cardinality cidx -> nclauses+cidx.
static inline int yals_cc_id (Yals * yals, int cidx, int type) {
  return type == TYPECLAUSE ? cidx : yals->nclauses + cidx;
}

// Component id of a constraint (cc_comp must be built).
static inline int yals_cc_comp_of (Yals * yals, int cidx, int type) {
  return yals->ddfw.cc_comp[yals_cc_id (yals, cidx, type)];
}

// Build connected components over shared-literal connectivity. Idempotent:
// only builds once (cc_comp stays valid for the lifetime of the formula).
static void yals_build_components (Yals * yals) {
  int N, v, s, occ, * p, * occs, cidx, first;
  if (yals->ddfw.cc_comp) return;       // already built
  N = yals->nclauses + yals->card_nclauses;
  if (N <= 0) return;
  int * parent = malloc (N * sizeof (int));
  for (int i = 0; i < N; i++) parent[i] = i;

  for (v = 1; v < yals->nvars; v++) {
    for (s = 0; s < 2; s++) {
      int lit = s ? -v : v;
      first = -1;
      occs = yals_occs (yals, lit);            // clauses containing lit
      for (p = occs; (occ = *p) >= 0; p++) {
        cidx = occ >> LENSHIFT;
        if (first < 0) first = cidx;
        else yals_cc_union (parent, first, cidx);
      }
      occs = yals_card_occs (yals, lit);        // cardinality containing lit
      for (p = occs; (occ = *p) >= 0; p++) {
        cidx = yals->nclauses + (occ >> LENSHIFT);
        if (first < 0) first = cidx;
        else yals_cc_union (parent, first, cidx);
      }
    }
  }

  yals->ddfw.cc_comp = malloc (N * sizeof (int));
  for (int i = 0; i < N; i++) yals->ddfw.cc_comp[i] = yals_cc_find (parent, i);

  // count distinct components
  int ncomp = 0;
  for (int i = 0; i < N; i++) if (yals->ddfw.cc_comp[i] == i) ncomp++;
  yals_msg (yals, 0,
    "componentlock: %d constraints (%d clauses + %d card) in %d connected components",
    N, yals->nclauses, yals->card_nclauses, ncomp);
  free (parent);
}

/*

  Get a random satisfied constraint with weight greater or equal to the initial weight.

  Select between a clause or cardinality consrtaint with weighted probability based
  on the number of each constraint type.

  May loop and waste time but probably very important for taking weight
  from other neighborhoods.

  Loop until a certain cutoff, if no source found with weight greater
  than initial weight, return the best weighted constraint found
  to that point.

  If componentlock is enabled, sink_comp is the sink's component id and only
  sources in the same component are accepted; pass sink_comp = -1 to disable.

*/
int yals_ddfw_get_random_sat_clause (Yals * yals, int * constraint_type, int sink_comp) {
    int source = -1;
    int selection, cnt = -1;
    int cnt_cutoff = 1000;// number of iterations before giving up

    int relative = (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights);

    bool get_something = true; // if cnt_cutoff is reached, select best so far, otherwise return Nothing
    int best_idx_card = -1;
    double best_wt_card = 0;
    int best_idx_cls = -1;
    double best_wt_cls = 0;

    int takes_hard, takes_soft;
    int source_hard = 0;

    takes_hard = takes_soft = 1;

    // check if source can be hard or soft
    if (yals->using_maxs_weights && !yals->current_weight_transfer_soft && !yals->opts.maxs_hard_takes_soft.val)
      takes_soft = 0;
    if (yals->using_maxs_weights && yals->current_weight_transfer_soft && !yals->opts.maxs_soft_takes_hard.val)
      takes_hard = 0;
    
    LOG ("Get random SAT clause");

    while (source < 0) {
      cnt++;
      if (cnt > cnt_cutoff) { // if looping a lot just abort
        yals_check_global_weight_invariant (yals);
        // yals_abort (yals, "looping on random sat clause");
        yals->stats.get_random_sat_missed += 1;
        break;
      }

      // weighted selection of constraint based on number of a particular consrtaint type

      if (yals->using_maxs_weights && yals->is_pure && yals->cardinality_is_hard && !yals->current_weight_transfer_soft && !yals->opts.maxs_hard_takes_soft.val) {
        // middle mile optimization (cardinality constraints are all hard)
        selection = yals_rand_mod (yals, INT_MAX) % (yals->card_nclauses);
        selection += yals->nclauses;
      } else {
        selection = yals_rand_mod (yals, INT_MAX) % (yals->nclauses + yals->card_nclauses);
      }

      if (selection < yals->nclauses) { // clause
        int clause = yals_rand_mod (yals, INT_MAX) % yals->nclauses;
        LOG ("Try %d with %d and %lf", clause, yals_satcnt (yals, clause) ,yals->ddfw.ddfw_clause_weights [clause] );
        
        source_hard = yals->hard_clause_ids [clause];
        if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

        // componentlock: only take from a source in the sink's component
        if (sink_comp >= 0 && yals_cc_comp_of (yals, clause, TYPECLAUSE) != sink_comp) continue;

        if (yals_satcnt (yals, clause) > 0) {
          if (get_something) {
            if (yals->ddfw.ddfw_clause_weights [clause] > best_wt_cls) {
                best_idx_cls = clause;
                best_wt_cls = yals->ddfw.ddfw_clause_weights [clause];
              }
          }
          if (relative && !source_hard) {
            if (yals->ddfw.ddfw_clause_weights [clause] > PEEK (yals->maxs_clause_weights, clause)) {
              source = clause;
              *constraint_type = TYPECLAUSE;
            }
          } else {
            if (yals->ddfw.ddfw_clause_weights [clause] >= yals->opts.init_clause_weight.val) {
              source = clause;
              *constraint_type = TYPECLAUSE;
            }
          }          
        }
      } else { // cardinality constraint
        int card = yals_rand_mod (yals, INT_MAX) % yals->card_nclauses;
        LOG ("Try constraint %d with %d and %d and %lf", card, yals_card_satcnt (yals, card),yals_card_bound (yals, card) ,yals->ddfw.ddfw_card_weights [card] );
        
        source_hard = yals->hard_card_ids [card];
        if ((source_hard && !takes_hard) || (!source_hard && !takes_soft)) continue;

        // componentlock: only take from a source in the sink's component
        if (sink_comp >= 0 && yals_cc_comp_of (yals, card, TYPECARDINALITY) != sink_comp) continue;

        if (yals_card_satcnt (yals, card) >= yals_card_bound (yals, card)) {
          if (get_something) {
            if (yals->ddfw.ddfw_card_weights [card] >= best_wt_card) {
              best_idx_card = card;
              best_wt_card = yals->ddfw.ddfw_card_weights [card];
            }
          }
          if (relative && !source_hard) {
            if (yals->ddfw.ddfw_card_weights [card] > PEEK (yals->maxs_card_weights, card)) {
              source = card;
              *constraint_type = TYPECARDINALITY;
            }
          } else {
            if (yals->ddfw.ddfw_card_weights [card] >= yals->opts.init_card_weight.val) {
              source = card;
              *constraint_type = TYPECARDINALITY;
            }
          }
        } 
      }
    }

    yals->stats.get_random_sat_cnt += cnt; // update miss statistics

    if (source == -1 && get_something) { // assign source to best weighted satisfied constraint found
      source = best_idx_card;
      *constraint_type = TYPECARDINALITY;
      if (best_wt_cls > best_wt_card) {
          source = best_idx_cls;
          *constraint_type = TYPECLAUSE;
      }
    }

    return source;
}


/*
  get weight that will be transfered from source to sink

  weight transfer determined by type of constraint the source is

  might create different linear weight transfer rule for cardinality consrtaints
  with different parameters
*/
double yals_ddfw_get_weight (Yals *yals, int source, int sink, int constraint_type_source, int constraint_type_sink) {
  double w = 0.0;

  // transfer large quantity of weight if you are still keeping initial weight
  if (yals->opts.wt_transfer_all.val) {
    double percent_take = yals->opts.wt_transfer_all.val / 10.0; // percentage to tranfer
    if (!yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights) {
      if (constraint_type_source == TYPECLAUSE && 
      yals->opts.init_clause_weight.val == yals->ddfw.ddfw_clause_weights [source])
        return percent_take * yals->opts.init_clause_weight.val;
      else if (constraint_type_source == TYPECARDINALITY && 
      yals->opts.init_card_weight.val == yals->ddfw.ddfw_card_weights [source])
        return percent_take * yals->opts.init_card_weight.val;
    } else {
      int soft = 0;
      if (constraint_type_source == TYPECLAUSE) {
        if (yals->using_maxs_weights && !yals->hard_clause_ids[source])
          soft = 1;
        if (soft && PEEK (yals->maxs_clause_weights, source) == yals->ddfw.ddfw_clause_weights [source])
          return percent_take * yals->ddfw.ddfw_clause_weights [source];
        else if (!soft && yals->opts.init_clause_weight.val == yals->ddfw.ddfw_clause_weights [source])
          return percent_take * yals->opts.init_clause_weight.val;
      } else if (constraint_type_source == TYPECARDINALITY) {
        if (yals->using_maxs_weights && !yals->hard_card_ids[source])
          soft = 1;
        if (soft && PEEK (yals->maxs_card_weights, source) == yals->ddfw.ddfw_card_weights [source])
          return percent_take * yals->ddfw.ddfw_card_weights [source];
        else if (!soft && yals->opts.init_card_weight.val == yals->ddfw.ddfw_card_weights [source])
          return percent_take * yals->opts.init_card_weight.val;
      }
    }
  }


  if (constraint_type_source == TYPECLAUSE)
    w = linear_wt (yals, source, TYPECLAUSE);
  else if (constraint_type_source == TYPECARDINALITY)
    w = linear_wt (yals, source, TYPECARDINALITY);
  else yals_abort (yals, "incorrect constraint type");

  return w;
}

/*

  Given a sink clause, find a source and transfer weight from source to sink.

  Update the unsat and sat1 weights for both source and sink based on weight change.

*/
void yals_ddfw_transfer_weights_for_clause (Yals *yals, int sink)
{
  int constraint_type;
  int source = -1;
  int sink_comp = yals->opts.componentlock.val ? yals_cc_comp_of (yals, sink, TYPECLAUSE) : -1;

  LOGCIDX (sink, "Transfer weight to");

  // Find maximum weighted satisfied clause (source), which is in same sign neighborhood of cidx (sink)
  // (same-sign neighbors share a literal with the sink, so are always in its component)
  source = yals_ddfw_get_max_weight_sat_clause (yals, sink, TYPECLAUSE, &constraint_type);

  if (source == -1)
    yals->ddfw.source_not_selected++;

  // If no such source is available (source=-1), then select a randomly satisfied clause as the source.
  if ( source == -1  || ( ( (double) yals_rand_mod (yals, INT_MAX) / (double) INT_MAX) <= yals->ddfw.clsselectp)) {
    source = yals_ddfw_get_random_sat_clause (yals, &constraint_type, sink_comp);
  }

  if (source == -1) {
    yals_msg (yals, 3, "could not find satisfied constraint to transfer from");
    return;
  }

  yals->ddfw.total_transfers++;

  assert (!yals_satcnt (yals, sink)); 

  if (constraint_type == TYPECLAUSE) {
    assert (yals_satcnt (yals, source)); // difference 1

    LOGCIDX (source, "Transfer weights from");

    double w = yals_ddfw_get_weight (yals, source,sink, constraint_type,TYPECLAUSE);

    LOG ("Transferring %lf",w);

    yals->ddfw.ddfw_clause_weights [source] -= w; // difference 2
    yals->ddfw.ddfw_clause_weights [sink] += w;
    if (yals->opts.litheap.val) { yals_nbr_update (yals, source); yals_nbr_update (yals, sink); }

    yals_ddfw_update_lit_weights_on_weight_transfer (yals, sink, source, constraint_type, TYPECLAUSE, w);

  } else if (constraint_type == TYPECARDINALITY) {
    assert (yals_card_satcnt (yals, source) >= yals_card_bound (yals, source));

    LOGCARDCIDX (source, "Transfer weights from");

    double w = yals_ddfw_get_weight (yals, source,sink, constraint_type,TYPECLAUSE);

    LOG ("Transferring %lf",w);

    yals->ddfw.ddfw_card_weights [source] -= w;
    yals->ddfw.ddfw_clause_weights [sink] += w;
    if (yals->opts.litheap.val) { yals_nbr_update (yals, yals->nclauses + source); yals_nbr_update (yals, sink); }

    yals_ddfw_update_lit_weights_on_weight_transfer (yals, sink, source, constraint_type, TYPECLAUSE, w);

  }

}

/*

  Given a sink cardinality constraint, find a source and transfer weight from source to sink.

  Update the unsat and sat1 weights for both source and sink based on weight change.

  Kept as separate function from a clause in case we want to handle it much differently...

*/
void yals_ddfw_transfer_weights_for_card (Yals *yals, int sink)
{
  int constraint_type;
  int source = -1;
  int sink_comp = yals->opts.componentlock.val ? yals_cc_comp_of (yals, sink, TYPECARDINALITY) : -1;

  LOGCARDCIDX (sink, "Transfer weight to");

  // Find maximum weighted satisfied clause (source), which is in same sign neighborhood of cidx (sink)
  source = yals_ddfw_get_max_weight_sat_clause (yals, sink, TYPECARDINALITY, &constraint_type);

  if (source == -1)
    yals->ddfw.source_not_selected++;

  // If no such source is available (source=-1), then select a randomly satisfied clause as the source.
  if ( source == -1  || ( ( (double) yals_rand_mod (yals, INT_MAX) / (double) INT_MAX) <= yals->ddfw.clsselectp)) {
    source = yals_ddfw_get_random_sat_clause (yals, &constraint_type, sink_comp);
  }

  if (source == -1) {
    yals_msg (yals, 3, "could not find sat clause to transfer from");
    return;
  }

  yals->ddfw.total_transfers++;

  assert (yals_card_satcnt (yals, sink)  < yals_card_bound (yals, sink));

  if (constraint_type == TYPECLAUSE) {
    assert (yals_satcnt (yals, source)); // difference 1

    LOGCIDX (source, "Transfer weights from");

    double w = yals_ddfw_get_weight (yals, source,sink, constraint_type,TYPECARDINALITY);

    LOG ("Transferring %lf",w);

    yals->ddfw.ddfw_clause_weights [source] -= w; // difference 2
    yals->ddfw.ddfw_card_weights [sink] += w;
    if (yals->opts.litheap.val) { yals_nbr_update (yals, source); yals_nbr_update (yals, yals->nclauses + sink); }

    yals_ddfw_update_lit_weights_on_weight_transfer (yals, sink, source, constraint_type, TYPECARDINALITY, w);

  } else if (constraint_type == TYPECARDINALITY) {
    assert (yals_card_satcnt (yals, source) >= yals_card_bound (yals, source));

    LOGCARDCIDX (source, "Transfer weights from");

    double w = yals_ddfw_get_weight (yals, source,sink, constraint_type,TYPECARDINALITY);

    LOG ("Transferring %lf",w);

    yals->ddfw.ddfw_card_weights [source] -= w;
    yals->ddfw.ddfw_card_weights [sink] += w;
    if (yals->opts.litheap.val) { yals_nbr_update (yals, yals->nclauses + source); yals_nbr_update (yals, yals->nclauses + sink); }

    yals_ddfw_update_lit_weights_on_weight_transfer (yals, sink, source, constraint_type, TYPECARDINALITY, w);

  }

}

// Loop over all falsified constraints and transfer weight to them
void yals_ddfw_transfer_weights (Yals *yals)
{
  double start = yals_time (yals);
  // Lnk * p;
  // // no queue implementation allowed
  // if (yals->unsat.usequeue)
  // {
  //   for (p = yals->unsat.queue.first; p; p = p->next)
  //       yals_ddfw_transfer_weights_for_clause (yals, p->cidx);
  // }
  // else

    // hard clauses
    for (int c = 0; c < COUNT(yals->unsat.stack); c++) {
      int cidx = PEEK (yals->unsat.stack, c);
      yals_ddfw_transfer_weights_for_clause (yals, cidx);   
    }

    // hard constraints
    for (int c = 0; c < COUNT(yals->card_unsat.stack); c++) {
      int cidx = PEEK (yals->card_unsat.stack, c);
      yals_ddfw_transfer_weights_for_card (yals, cidx);
    }


    if (yals->using_maxs_weights && yals->weight_transfer_soft) {
      yals->current_weight_transfer_soft = 1;
      // soft clauses
      for (int c = 0; c < COUNT(yals->unsat_soft.stack); c++) {
        int cidx = PEEK (yals->unsat_soft.stack, c);
        yals_ddfw_transfer_weights_for_clause (yals, cidx);   
      }

      // soft constraints
      for (int c = 0; c < COUNT(yals->card_unsat_soft.stack); c++) {
        int cidx = PEEK (yals->card_unsat_soft.stack, c);
        yals_ddfw_transfer_weights_for_card (yals, cidx);  // TODO this function
      }
      yals->current_weight_transfer_soft = 0;

    }

  if (!yals->ddfw.guaranteed_uwrvs)
    yals->ddfw.missed_guaranteed_uwvars++;
  yals->ddfw.wt_count++;
  yals->ddfw.guaranteed_uwrvs = 0;

  yals->stats.maxs_time.weight_transfer += yals_time (yals) - start;
}

static void yals_init_outer_restart_interval (Yals * yals) {
  if (yals->opts.restartouter.val) {
    yals->limits.restart.outer.interval = yals_outer_restart_interval (yals);
    yals->limits.restart.outer.lim =
      yals->stats.flips + yals->limits.restart.outer.interval;
    yals_msg (yals, 1,
      "initial outer restart limit at %lld flips",
      yals->limits.restart.outer.lim);
  } else {
    yals_msg (yals, 1, "outer restarts disabled");
    yals->limits.restart.outer.lim = YALS_INT64_MAX;
  }
}

static void yals_restart_outer (Yals * yals) {
  double start = yals_time (yals);
  unsigned long long seed;
  int64_t interval;
  yals->stats.restart.outer.count++;
  seed = yals_rand (yals);
  seed |= ((unsigned long long) yals_rand (yals)) << 32;
  yals_srand (yals, seed);
  interval = yals->limits.restart.outer.interval;
  if (yals->limits.restart.outer.interval <= YALS_INT64_MAX/2)
    yals->limits.restart.outer.interval *= 2;
  else yals->limits.restart.outer.interval = YALS_INT64_MAX;
  if (YALS_INT64_MAX - yals->stats.flips >= interval)
    yals->limits.restart.outer.lim = yals->stats.flips + interval;
  else
    yals->limits.restart.outer.lim = YALS_INT64_MAX;
  yals_msg (yals, 1,
    "starting next outer restart round %lld after %.2f seconds",
    (long long) yals->stats.restart.outer.count, yals_sec (yals));
  yals_msg (yals, 1, "current seed %llu", seed);
  yals_msg (yals, 1,
    "next outer restart limit %lld",
    (long long) yals->limits.restart.outer.lim);
  yals_reset_cache (yals);
  yals->stats.time.restart += yals_time (yals) - start;
}

static void yals_outer_loop (Yals * yals) {
  yals_init_outer_restart_interval (yals);
  // for (;;) {
    yals_set_default_strategy (yals);  // for probsat it appears
    yals_fix_strategy (yals); // for probsat it appears
    yals_pick_assignment (yals, 1);
    yals_update_sat_and_unsat (yals);
    yals->stats.tmp = INT_MAX;
    yals_save_new_minimum (yals);
    yals->stats.last = yals_nunsat (yals);

    // cardinality constraint version only uses call to yals_inner_loop_max_tries
    if (!yals->opts.maxtries.val) yals->opts.maxtries.val = 1;
    if (!yals->opts.cutoff.val && yals->limits.flips) yals->opts.cutoff.val = yals->limits.flips;

    yals_inner_loop_max_tries (yals);

    // if (yals->opts.maxtries.val && yals->opts.cutoff.val)
    // {
      //  if (yals_inner_loop_max_tries (yals))  // this always returns a non-zero value...
      //   return;
    // }

}

/*------------------------------------------------------------------------*/

// checking clauses
// debugging todo: check cardinality constraints
// debugging todo: count for maxsat
// currently using external tool (check-sat) for checking
static void yals_check_assignment (Yals * yals) {
  const int * c = yals->cdb.start;
  while (c < yals->cdb.top) {
    int satisfied = 0, lit;
    while ((lit = *c++))
      satisfied += yals_best (yals, lit);
    if (!satisfied)
      yals_abort (yals,
"internal error in 'yals_sat' (invalid satisfying assignment)");
  }
}

// check after preprocessing (unit propagation) if all variables are assigned
int yals_all_assigned (Yals * yals) {
  if (SIZE (yals->card_cdb) == 0 && SIZE (yals->cdb) == 0) {
    yals_set_units (yals);
    yals_save_new_minimum (yals);
    LOG ("Yals all assigned");
    return 1;
  }
  return 0;
}

static int yals_lkhd_internal (Yals * yals) {
  int64_t maxflips;
  int res = 0, idx;
  if (!yals->flips) goto DONE;
  maxflips = -1;
  for (idx = 1; idx < yals->nvars; idx++) {
    int64_t tmpflips = yals->flips[idx];
    if (tmpflips <= maxflips) continue;
    res = idx, maxflips = tmpflips;
  }
  if (res &&
      yals->best &&
      !GETBIT (yals->best, yals->nvarwords, res))
    res = -res;
DONE:
  return res;
}

// score used for DDFW SAT algorithm
double basic_ddfw_score (Yals * yals, int var) {
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;

  double flip_gain =
        yals->ddfw.unsat_weights [get_pos (false_lit)]
        - yals->ddfw.sat1_weights [get_pos (true_lit)];
  LOG ("determine uwvar %d with gain %lf, unsat %lf, sat %lf", var, flip_gain,yals->ddfw.unsat_weights [get_pos (false_lit)], yals->ddfw.sat1_weights [get_pos (true_lit)]);

  // Snap near-zero gains to 0 so noisy residuals are treated as non-improving.
  // eps = flip_gain_eps_e4 / 10000 (0 disables).
  int e4 = yals->opts.flip_gain_eps_e4.val;
  if (e4 > 0) {
    double eps = e4 / 10000.0;
    if (flip_gain > -eps && flip_gain < eps) flip_gain = 0.0;
  }

  return flip_gain;
}

int yals_sat (Yals * yals) {
  int res, limited = 0, lkhd;
  if (!EMPTY (yals->clause))
    yals_abort (yals, "added clause incomplete in 'yals_sat'");

  if (yals->mt) {
    yals_msg (yals, 1, "original formula contains empty clause");
    return 20;
  }

  if (yals->opts.maxs_pure.val) {
    yals->is_pure = 1;
    yals->hard_polarity = yals->opts.maxs_pure_polarity.val;
  }

  if (yals->opts.prep.val && !EMPTY (yals->trail)) {
    yals_preprocess (yals);
    if (yals->mt) {
      yals_msg (yals, 1,
"formula after unit propagation contains empty clause");
      return 20;
    }
  }

  yals->stats.time.entered = yals_time (yals);

  if (yals->opts.setfpu.val) yals_set_fpu (yals);

  yals->pick = 0; // we only use the stack for unsat clauses

  yals_connect (yals);

  yals_card_connect (yals);

  if (yals_all_assigned (yals))
      return 10;

  yals_ddfw_init_build (yals);

  res = 0;
  limited += (yals->limits.flips >= 0);
#ifndef NYALSMEMS
  limited += (yals->limits.mems >= 0);
#endif
  if (!limited)
    yals_msg (yals, 1, "starting unlimited search");
  else {

    if (yals->limits.flips < 0)
      yals_msg (yals, 1,
"search not limited by the number of flips");
    else
      yals_msg (yals, 1,
"search limited by %lld flips",
(long long) yals->limits.flips);

#ifndef NYALSMEMS
    if (yals->limits.mems < 0)
      yals_msg (yals, 1,
"search not limited by the number of mems");
    else
      yals_msg (yals, 1,
"search limited by %lld mems",
(long long) yals->limits.mems);
#endif
  }

  if (yals->using_maxs_weights) {
    yals_maxs_outer_loop (yals);
  }
  else {
    yals->ddfw.uvars_heap.score_fun = basic_ddfw_score;
    yals->opts.init_card_weight.val = yals->opts.sat_ddfw_init_card_weight.val;
    yals_outer_loop (yals);
  }
  
  if (yals->using_maxs_weights) {
    assert (!yals->mt);
    if (!yals->stats.maxs_best_cost) {
      yals_print_strategy (yals, "winning strategy:", 1);
      yals_check_assignment (yals);
      res = 10;
    } else assert (!res);
  }
  else {
    assert (!yals->mt);
    if (!yals->stats.best) {
      yals_print_strategy (yals, "winning strategy:", 1);
      yals_check_assignment (yals);
      res = 10;
    } else assert (!res);
  }

  if ((lkhd = yals_lkhd_internal (yals)))
    yals_msg (yals, 1,
      "most flipped literal %d flipped %lld times",
      lkhd, (long long) yals->flips[ABS (lkhd)]);

  if (yals->opts.setfpu.val) yals_reset_fpu (yals);
  yals_flush_time (yals);
  return res;
}

/*------------------------------------------------------------------------*/

int yals_deref (Yals * yals, int lit) {
  if (!lit) yals_abort (yals, "zero literal argument to 'yals_val'");
  if (yals->mt || ABS (lit) >= yals->nvars) return lit < 0 ? 1 : -1;
  return yals_best (yals, lit) ? 1 : -1;
}

int yals_minimum (Yals * yals) { return yals->stats.best; }

long long yals_flips (Yals * yals) { return yals->stats.flips; }

long long yals_mems (Yals * yals) {
#ifndef NYALSMEMS
  return yals->stats.mems.all;
#else
  return 0;
#endif
}

int yals_lkhd (Yals * yals) {
  int res = yals_lkhd_internal (yals);
  if (res)
    yals_msg (yals, 1,
      "look ahead literal %d flipped %lld times",
      res, (long long) yals->flips [ABS (res)]);
  else
    yals_msg (yals, 2, "no look ahead literal found");
  return res;
}

/*------------------------------------------------------------------------*/

static void yals_minlits_cidx (Yals * yals, int cidx) {
  const int * lits, * p;
  int lit;
  assert_valid_cidx (cidx);
  lits = yals_lits (yals, cidx);
  for (p = lits; (lit = *p); p++)
    if (yals_best (yals, lit))
      return;
  for (p = lits; (lit = *p); p++) {
    int idx = ABS (lit);
    assert (idx < yals->nvars);
    if (yals->mark.start[idx]) continue;
    yals->mark.start[idx] = 1;
    PUSH (yals->minlits, lit);
  }
}

const int * yals_minlits (Yals * yals) {
  int count, cidx;
  RELEASE (yals->mark);
  while (COUNT (yals->mark) < yals->nvars)
    PUSH (yals->mark, 0);
  FIT (yals->mark);
  CLEAR (yals->minlits);
  for (cidx = 0; cidx < yals->nclauses; cidx++)
    yals_minlits_cidx (yals, cidx);
  count = COUNT (yals->minlits);
  yals_msg (yals, 1,
    "found %d literals in unsat clauses %.0f%%",
    count, yals_pct (count, yals->nvars));
  PUSH (yals->minlits, 0);
  RELEASE (yals->mark);
  FIT (yals->minlits);
  return yals->minlits.start;
}

/*------------------------------------------------------------------------*/

void yals_stats (Yals * yals) {

  yals_flush_time (yals);

  Stats * s = &yals->stats;
  double t = s->time.total;
  int64_t sum;

  if (yals->using_maxs_weights) {
    yals_msg (yals, 0, "Cost best %lf (tmp %lf), clauses %lf, constraints %lf",
    yals->stats.maxs_best_cost, yals->stats.maxs_tmp_weight,yals->stats.maxs_clause_best_weight, yals->stats.maxs_card_best_weight);

    yals_msg (yals, 0, "hard constraints best %d, clauses %d, constraints %d",
    yals->stats.maxs_best_hard_cnt, yals->stats.maxs_clause_best_hard_cnt, yals->stats.maxs_card_best_hard_cnt);

    yals_msg (yals, 0, "soft constraints best %d, clauses %d, constraints %d",
    yals->stats.maxs_best_soft_cnt, yals->stats.maxs_clause_best_soft_cnt, yals->stats.maxs_card_best_soft_cnt);

  }

  yals_msg (yals, 0,
    "minimum clauses %d minimum constraints %d",
    s->best_clauses, s->best_cardinality);
  yals_msg (yals, 0,
    "restart time %.3f seconds %.0f%%",
    s->time.restart, yals_pct (s->time.restart, s->time.total));
  yals_msg (yals, 0,
    "number of flips %d", s->flips);
  yals_msg (yals, 0,
    "restart time %.3f seconds %.0f%%",
    s->time.restart, yals_pct (s->time.restart, s->time.total));
  yals_msg (yals, 0,
    "%lld inner restarts, %lld maximum interval",
    (long long) s->restart.inner.count,
    (long long) s->restart.inner.maxint);
  yals_msg (yals, 0,
    "%lld outer restarts, %lld maximum interval",
    (long long) s->restart.outer.count,
    (long long) yals->limits.restart.outer.interval);
  sum = s->strat.def + s->strat.rnd;
  yals_msg (yals, 0,
    "default strategy %lld %.0f%%, random strategy %lld %.0f%%",
    (long long) s->strat.def, yals_pct (s->strat.def, sum),
    (long long) s->strat.rnd, yals_pct (s->strat.rnd, sum));
  yals_msg (yals, 0,
    "picked best=%lld cached=%lld keep=%lld pos=%lld neg=%lld rnd=%lld",
    (long long) s->pick.best, (long long) s->pick.cached,
    (long long) s->pick.keep, (long long) s->pick.pos,
    (long long) s->pick.neg, (long long) s->pick.rnd);
  sum = s->cache.inserted + s->cache.replaced;
  yals_msg (yals, 0,
    "cached %lld assignments, %lld replaced %.0f%%, %lld skipped, %d size",
    (long long) sum,
    (long long) s->cache.replaced, yals_pct (s->cache.replaced, sum),
    (long long) s->cache.skipped, (int) COUNT (yals->cache));
  sum = s->sig.falsepos + s->sig.truepos;
  yals_msg (yals, 0,
    "%lld sigchecks, %lld negative %.0f%%, "
    "%lld positive %.0f%%, %lld false %.0f%%",
    (long long) s->sig.search,
    (long long) s->sig.neg, yals_pct (s->sig.neg, s->sig.search),
    (long long) sum, yals_pct (sum, s->sig.search),
    (long long) s->sig.falsepos, yals_pct (s->sig.falsepos, s->sig.search));
  if (yals->unsat.usequeue) {
    yals_msg (yals, 0,
      "allocated max %d chunks %d links %lld unfair",
      s->queue.max.chunks, s->queue.max.lnks, (long long) s->queue.unfair);
    yals_msg (yals, 0,
      "%lld defragmentations in %.3f seconds %.0f%%",
      (long long) s->defrag.count,
      s->time.defrag, yals_pct (s->time.defrag, s->time.total));
    yals_msg (yals, 0,
      "moved %lld in total and %.1f on average per defragmentation",
      (long long) s->defrag.moved,
      yals_avg (s->defrag.moved, s->defrag.count));
  } else
    yals_msg (yals, 0, "maximum unsat stack size %d", s->maxstacksize);

#ifndef NYALSTATS
  yals_msg (yals, 0,
    "%lld broken, %.2f broken/flip, %lld made, %.2f made/flip",
    (long long) s->broken, yals_avg (s->broken, s->flips),
    (long long) s->made, yals_avg (s->made, s->flips));

  yals_msg (yals, 0,
    "%u maximum %u minimum sum of weighted breaks",
    s->wb.max, s->wb.min);
#endif

  yals_msg (yals, 0,
    "%.3f unsat clauses on average",
    yals_pct (s->unsum, s->flips));

#ifndef NYALSTATS
  if (s->inc && s->dec) {
    double suminc, sumdec, f = s->flips;
    int64_t ninc, ndec, ninclarge, ndeclarge;
    int len;
    assert (!s->dec[0]);
    assert (!s->inc[yals->maxlen]);
    suminc = sumdec = ninc = ndec = ndeclarge = ninclarge = 0;
    for (len = 0; len <= yals->maxlen; len++) {
      int64_t inc = s->inc[len];
      int64_t dec = s->dec[len];
      ninc += inc, ndec += dec;
      suminc += len * inc, sumdec += len * dec;
      if (len > 2) ninclarge += inc;
      if (len > 3) ndeclarge += dec;
    }
    yals_msg (yals, 0,
      "%lld incs %.3f avg satcnt, %lld decs %.3f avg satcnt",
      (long long) ninc, yals_avg (suminc, ninc),
      (long long) ndec, yals_avg (sumdec, ndec));
    yals_msg (yals, 0,
      "inc0 %.2f %.2f%%, inc1 %.2f %.2f%%, "
      "inc2 %.2f %.2f%%, incl %.2f %.2f%%",
      yals_avg (s->inc[0], f), yals_pct (s->inc[0], ninc),
      yals_avg (s->inc[1], f), yals_pct (s->inc[1], ninc),
      yals_avg (s->inc[2], f), yals_pct (s->inc[2], ninc),
      yals_avg (ninclarge, f), yals_pct (ninclarge, ninc));
    yals_msg (yals, 0,
      "dec1 %.2f %.2f%%, dec2 %.2f %.2f%%, "
      "dec3 %.2f %.2f%%, decl %.2f %.2f%%",
      yals_avg ( s->dec[1], f), yals_pct (s->dec[1], ndec),
      yals_avg (s->dec[2], f), yals_pct (s->dec[2], ndec),
      yals_avg (s->dec[3], f), yals_pct (s->dec[3], ndec),
      yals_avg (ndeclarge, f), yals_pct (ndeclarge, ndec));
  }
#endif

#ifndef NYALSMEMS
  {
    double M = 1000000.0;
    long long all = 0;

    all += s->mems.lits;
    all += s->mems.crit;
    all += s->mems.occs;
    all += s->mems.read;
    all += s->mems.update;
    all += s->mems.weight;

    assert (all == s->mems.all);

    yals_msg (yals, 0,
      "megamems: %.0f all 100%, %.0f lits %.0f%%, %.0f crit %.0f%%, "
      "%.0f weight %.0f%%",
      all/M,
      s->mems.lits/M, yals_pct (s->mems.lits, all),
      s->mems.crit/M, yals_pct (s->mems.crit, all),
      s->mems.weight/M, yals_pct (s->mems.weight, all));

    yals_msg (yals, 0,
      "megamems: %.0f occs %.0f%%, %.0f read %.0f%%, %.0f update %.0f%%",
      s->mems.occs/M, yals_pct (s->mems.occs, all),
      s->mems.read/M, yals_pct (s->mems.read, all),
      s->mems.update/M, yals_pct (s->mems.update, all));

    yals_msg (yals, 0,
      "%.1f million mems per second, %.1f mems per flip",
      yals_avg (all/1e6, t), yals_avg (all, s->flips));
  }
#endif

  yals_msg (yals, 0,
    "%.1f seconds searching, %.1f MB maximally allocated (%lld bytes)",
    t, s->allocated.max/(double)(1<<20), (long long) s->allocated.max);

  yals_msg (yals, 0,
    "%lld flips, %.1f thousand flips per second, %lld break zero %.1f%%",
    (long long) s->flips, yals_avg (s->flips/1e3, t),
    s->bzflips, yals_pct (s->bzflips, s->flips));

  yals_msg (yals, 0,
    "%lld get random sat misses and count %lld",
    (long long) s->get_random_sat_cnt,(long long) s->get_random_sat_missed);

  yals_msg (yals, 0,
    "minimum %d hit %lld times, maximum %d",
    s->best, (long long) s->hits, s->worst);

  yals_msg (yals, 0,
    "initialization time %lf percentage of total %lf",
    s->maxs_time.initialization, yals_pct(s->maxs_time.initialization,s->time.total));
  yals_msg (yals, 0,
    "make time %lf percentage of total %lf",
    s->maxs_time.make_time, yals_pct(s->maxs_time.make_time,s->time.total));
  yals_msg (yals, 0,
    "break time %lf percentage of total %lf",
    s->maxs_time.break_time, yals_pct(s->maxs_time.break_time,s->time.total));
  yals_msg (yals, 0,
    "weigh transfer time %lf percentage of total %lf",
    s->maxs_time.weight_transfer, yals_pct(s->maxs_time.weight_transfer,s->time.total));
  yals_msg (yals, 0,
    "variable selection time %lf percentage of total %lf",
    s->maxs_time.var_selection, yals_pct(s->maxs_time.var_selection,s->time.total));
  yals_msg (yals, 0,
    "soft variable selection time %lf percentage of total %lf",
    s->maxs_time.soft_var_selection, yals_pct(s->maxs_time.soft_var_selection,s->time.total));
  yals_msg (yals, 0,
    "hard variable selection time %lf percentage of total %lf",
    s->maxs_time.hard_var_selection, yals_pct(s->maxs_time.hard_var_selection,s->time.total));
}

/** ---------------- Start of DDFW ------------------------ **/

void set_options (Yals * yals)
{
  yals->ddfw.pick_method = yals->opts.ddfwpicklit.val;
  yals->inner_restart = !yals->opts.innerrestartoff.val;
}

void yals_init_ddfw (Yals *yals)
{
  set_options (yals);
  if (yals->opts.componentlock.val) yals_build_components (yals); // builds once
  yals->ddfw.clsselectp = (double) yals->opts.clsselectp.val / 100.0;
  yals->ddfw.ddfw_active = 1;
  yals->ddfw.recent_max_reduction = -1;
  yals->last_flip_unsat_count = -1;
  yals->consecutive_non_improvement = 0;
  yals->ddfw.flip_span = 0;
  yals->ddfw.alg_switch = 0;
  yals->ddfw.prob_check_window = 100;


  yals->ddfw.max_weighted_neighbour = calloc(yals->nclauses, sizeof (int));
  yals->ddfw.break_weight = 0;
  yals->ddfw.local_minima = 0;
  yals->ddfw.wt_count = 0;

  yals->ddfw.conscutive_lm = 0;
  yals->ddfw.count_conscutive_lm = 0;
  yals->ddfw.consecutive_lm_length = 0;
  yals->ddfw.max_consecutive_lm_length = -1;

  yals->ddfw.guaranteed_uwrvs = 0;
  yals->ddfw.missed_guaranteed_uwvars = 0;
  yals->ddfw.sideways = 0;

  yals->ddfw.init_weight_done = 0;

  yals->ddfw.sat_count_in_clause = calloc (yals->nclauses, sizeof (int));
  yals->ddfw.helper_hash_clauses = calloc (yals->nclauses, sizeof (int));
  yals->ddfw.helper_hash_vars = calloc (yals->nvars, sizeof (int));

  yals->ddfw.ddfw_clause_weights = malloc (yals->nclauses* sizeof (double));
  yals->ddfw.unsat_weights = calloc (2* yals->nvars, sizeof (double));
  yals->ddfw.sat1_weights = calloc (2* yals->nvars, sizeof (double));
  yals->ddfw.uwrvs = calloc (yals->nvars, sizeof (int));
  yals->ddfw.uwvars_gains = calloc (yals->nvars, sizeof (double));
  yals->ddfw.non_increasing = calloc (yals->nvars, sizeof (int));

  yals->ddfw.uvar_pos = malloc (yals->nvars* sizeof (int)); 
  yals->ddfw.uvar_changed_pos = malloc (yals->nvars* sizeof (int)); 

  yals->ddfw.var_unsat_count = calloc (yals->nvars, sizeof (int)); 

  memset (&yals->ddfw.uvars_heap, 0 , sizeof (yals->ddfw.uvars_heap));
  yals_resize_heap (yals, &yals->ddfw.uvars_heap, yals->nvars);

  if (yals->using_maxs_weights) {
    memset (&yals->ddfw.uvars_heap_soft, 0 , sizeof (yals->ddfw.uvars_heap_soft));
    yals_resize_heap (yals, &yals->ddfw.uvars_heap_soft, yals->nvars);
    yals->ddfw.uvar_pos_soft = malloc (yals->nvars* sizeof (int));
    yals->ddfw.var_unsat_count_soft = calloc (yals->nvars, sizeof (int));
    yals->ddfw.unsat_weights_soft = calloc (2* yals->nvars, sizeof (double));
    yals->ddfw.sat1_weights_soft = calloc (2* yals->nvars, sizeof (double));
     for (int i=1; i< yals->nvars; i++) {
      yals->ddfw.uvar_pos_soft [i] = -1;
    }
  }

  for (int i=0; i< yals->nclauses; i++) {

    if (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights) {
      
      if (yals->hard_clause_ids [i])
        yals->ddfw.ddfw_clause_weights [i] = PEEK (yals->maxs_clause_weights, i);
      else 
        yals->ddfw.ddfw_clause_weights [i] = yals->opts.init_clause_weight.val;
    }
    else
      yals->ddfw.ddfw_clause_weights [i] = yals->opts.init_clause_weight.val;

  }

  for (int i=1; i< yals->nvars; i++) {
    yals->ddfw.uvar_pos [i] = -1;
    yals->ddfw.uvar_changed_pos [i] = -1;
  }

  yals->ddfw.weight_update_time = 0; yals->ddfw.uwrv_time = 0; yals->ddfw.flip_time = 0; 
  yals->ddfw.wtransfer_time = 0; yals->ddfw.neighborhood_comp_time = 0;
  yals->ddfw.update_candidate_sat_clause_time = 0; yals->ddfw.compute_uwvars_from_unsat_clauses_time = 0;
  yals->ddfw.init_neighborhood_time = 0;
  /* IDEA: compute neighborhood for all the clauses, if clause-to-variable ratio is less than a threshold X
   EG: yals->ddfw.neighbourhood_at_init = ((double) yals->nclauses / (double) yals->nvars) <= X ? 1 : 0*/
  yals->ddfw.neighbourhood_at_init = 0; //((double) yals->nclauses / (double) yals->nvars) <= 100 ? 1 : 0;
  yals->ddfw.time_ddfw = 0;

  yals->ddfw.flips_ddfw_temp = 0; 
  yals->ddfw.flips_ddfw = 0;
  yals->ddfw.sum_uwr = 0;
  yals->ddfw.source_not_selected = 0;
  yals->ddfw.total_transfers = 0;

  /*
    cardinality constraint initializations
  */
  yals->ddfw.ddfw_card_weights = malloc (yals->card_nclauses* sizeof (double));
  // yals->ddfw.card_clause_calculated_weights = malloc (yals->card_nclauses* sizeof (double));
  yals->ddfw.card_sat_count_in_clause = calloc (yals->card_nclauses, sizeof (int));
  yals->ddfw.card_helper_hash_clauses = calloc (yals->card_nclauses, sizeof (int));
  for (int i = 0; i < yals->card_nclauses; i++) {
     if (yals->opts.maxs_init_weight_relative.val && yals->using_maxs_weights) {
      
      if (yals->hard_card_ids [i])
        yals->ddfw.ddfw_card_weights [i] = PEEK (yals->maxs_card_weights, i);
      else 
        yals->ddfw.ddfw_card_weights [i] = yals->opts.init_card_weight.val;
    }
    else
      yals->ddfw.ddfw_card_weights [i] = yals->opts.init_card_weight.val;
  }

  /*
    MaxSAT initialization
  */
  yals->weight_transfer_soft = 0;
  yals->current_weight_transfer_soft = 0;

  // --litheap: build per-literal neighbor heaps now that all weights are set.
  yals->ddfw.nbr_built = 0;
  if (yals->opts.litheap.val) yals_nbr_build (yals);

}





/*
  When changing the scoring function of a heap, we need to go through
  and reupdate scores. Not a part of heap API. We could pop all 
  elements then push again with new scores. Maybe that is faster 
  than inline updates, but would require popping all elements (each pop
  leads to a bubble down operation for the element from Last that
  replaced the max element)
*/
void yals_ddfw_update_score_function_weights (Yals * yals) {
  int var;
  double score;
  STACK_INT vars_on;
  INIT (vars_on);

  yals_msg (yals, 1, "updating scores");

  // remove everything from heap
  while (!yals_empty_heap (&yals->ddfw.uvars_heap)) {
    var = yals_pop_max_heap (yals, &yals->ddfw.uvars_heap);
    PUSH (vars_on, var);
  }

  // add back to heap with updated score function
  while (!EMPTY (vars_on)) {
    var = POP (vars_on);
    score = (yals->ddfw.uvars_heap.score_fun) (yals, var);
    yals_update_heap (yals, &yals->ddfw.uvars_heap, var, score);
  }

  RELEASE (vars_on);
}

/*

  After a flip, we store all changed variables in uvar_changed.

  Loop through these variables and update their weight change on 
  the score heap.

*/
void yals_ddfw_update_changed_var_weights (Yals * yals) {
  int var, *pos, polarity;
  int nChanged = COUNT (yals->ddfw.uvars_changed);
  double score;

  for (pos = yals->ddfw.uvars_changed.start; pos != yals->ddfw.uvars_changed.top; pos++) {
    var = ABS(*pos);

    yals->ddfw.uvar_changed_pos[var] = -1;
    polarity = yals_polarity (yals, var);
    if (yals->is_pure) {
      // hard constraints
      if (polarity != yals->hard_polarity) {
        if (!yals->ddfw.var_unsat_count[var]) { // remove from heap
          if (yals_heap_contains (&yals->ddfw.uvars_heap, var))
            yals_pop_heap (yals, &yals->ddfw.uvars_heap, var);
        } else {
          score = (yals->ddfw.uvars_heap.score_fun) (yals, var);
          yals_update_heap (yals, &yals->ddfw.uvars_heap, var, score);
        }
      }
      else {
        // soft constraints
        if (!yals->ddfw.var_unsat_count_soft[var]) { // remove from heap
          if (yals_heap_contains (&yals->ddfw.uvars_heap_soft, var))
            yals_pop_heap (yals, &yals->ddfw.uvars_heap_soft, var);
        } else {
          score = (yals->ddfw.uvars_heap_soft.score_fun) (yals, var);
          yals_update_heap (yals, &yals->ddfw.uvars_heap_soft, var, score);
        }
      }
    } else if (yals->using_maxs_weights) {
      // hard
      score = (yals->ddfw.uvars_heap.score_fun) (yals, var); // heap has a scoring function
      if (!yals->ddfw.var_unsat_count[var] && !yals->ddfw.var_unsat_count_soft[var]) { // remove from heap
        if (yals_heap_contains (&yals->ddfw.uvars_heap, var))
          yals_pop_heap (yals, &yals->ddfw.uvars_heap, var);
        continue;
      }
      yals_update_heap (yals, &yals->ddfw.uvars_heap, var, score);
    }
    else { // normal sat problem
      if (!yals->ddfw.var_unsat_count[var]) { // remove from heap
        if (yals_heap_contains (&yals->ddfw.uvars_heap, var))
          yals_pop_heap (yals, &yals->ddfw.uvars_heap, var);
        continue;
      }
      score = (yals->ddfw.uvars_heap.score_fun) (yals, var); // heap has a scoring function
      if (score <= 0 && !yals_heap_contains (&yals->ddfw.uvars_heap, var))
        continue;
      yals_update_heap (yals, &yals->ddfw.uvars_heap, var, score);
    }
  }
  CLEAR (yals->ddfw.uvars_changed);

  // update stats with nChanged (to compare vs size of uvars to loop over...)
  yals->stats.nheap_updated += nChanged;
}

// get random uvar off the heap
int yals_get_random_uvar (Yals * yals, int soft) {
  STACK_INT *uvars;
  if (yals->using_maxs_weights && soft) {
    uvars = &yals->ddfw.uvars_soft;
  }
  else {
    uvars = &yals->ddfw.uvars;
  }

  int cnt = COUNT (*uvars);
  int pos = yals_rand_mod (yals, cnt);

  return PEEK (*uvars, pos);
}

/* 

  Grab a literal from the heap to flip.

  Can either use stochastic selection or 
  pick the best literal.

  Return 0 if no literals on the heap.

*/
int yals_pick_literal_from_heap (Yals * yals, int soft) {
  int lit = 0, selectCnt;
  heap *heap;
  if (soft) {
    heap = &yals->ddfw.uvars_heap_soft;
    selectCnt = yals->opts.maxs_soft_stochastic_selection.val;
  }
  else {
    heap = &yals->ddfw.uvars_heap;
    selectCnt = yals->opts.hard_stochastic_selection.val;
  }

  yals_ddfw_update_changed_var_weights (yals);

  if (COUNT (heap->stack)) {

    if ((int) yals_rand_mod (yals, 100000) <=  yals->opts.random_select.val) {
      // random literal
      int cnt = COUNT (heap->stack);
      int pos = yals_rand_mod (yals, cnt);
      lit = PEEK (heap->stack, pos);

      yals_pop_heap (yals, heap, abs (lit));

      yals->ddfw.best_var = lit;
      yals->ddfw.best_weight = yals_get_heap_score (heap, lit);
    } else {

      if (selectCnt > 1) { // stochastic selection 
        int choice_of = MIN (COUNT (heap->stack), selectCnt);
        int added_lits = 0;
        CLEAR (yals->lit_scores);

        for (int i = 0; i < choice_of; i++) {
          Lit_Score temp;
          temp.lit = yals_pop_max_heap (yals, heap);
          temp.score = yals_get_heap_score (heap, temp.lit);
          if (temp.score <= 0) continue;
          if (yals->opts.select_exp.val > 1) {
            temp.score = pow (temp.score, (yals->opts.select_exp.val/10000.0));
          }
          PUSH (yals->lit_scores, temp);
          added_lits++;
        }
        if (added_lits)
          lit = yals_pick_from_list_scores (yals); // weighted choice from lit_scores

        // push back non-selected variables
        int sCnt = COUNT (yals->lit_scores);
        for (int i = 0; i < sCnt; i++) {
          Lit_Score temp = POP (yals->lit_scores);
          if (temp.lit == lit) continue;
          yals_update_heap (yals,heap,temp.lit,temp.score);
        }

      } else {
        lit = yals_pop_max_heap (yals, heap);
        yals->ddfw.best_var = lit;
        yals->ddfw.best_weight = yals_get_heap_score (heap, lit);
      }
    }
  }

  yals_check_global_best_weight_invariant (yals);

  // score less than or equal to 0 is not flipped (not weight reducing)
  // todo: handle sideways flips
  if (lit && !yals->using_maxs_weights && yals->ddfw.uvars_heap.score_fun (yals,lit) <= 0)
    lit = 0;

  if (lit) // as it occurs in current assignment
    lit = yals_val (yals, lit) ? lit : -lit;

  LOG ("Picking literal %d with weight %lf", lit, yals->ddfw.best_weight);

  return lit;
}

// outdated, now use a heap
void determine_uwvar (Yals *yals , int var)
{
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;
  /**
      FLIP: true_lit ---> false_lit
      1) unsat_weights [get_pos (false_lit)]
      is the GAINS of satisfied weight with FLIP: cumilative weights of the currently unsatisfied clauses,
      where false_lit appears. If true_lit is filpped to false_lit, these clauses will become satisfied.
     
      2) sat1_weights [get_pos (true_lit)];
      is the LOSS of satisfied weight with FLIP: cumilative weights of the currently
      critically satisfied (where only true_lit is satisfied) clauses, where true_lit appears.
      If true_lit is filpped to false_lit, these clauses will become satisfied.
     
      3) if GAINS (of satisfaction) - LOSS (of satisfaction) > 0, it implies reduction of UNSAT weights.
  **/
  double flip_gain =
        yals->ddfw.unsat_weights [get_pos (false_lit)]  
        - yals->ddfw.sat1_weights [get_pos (true_lit)];
  LOG ("determine uwvar %d with gain %lf", var, flip_gain);

  if (flip_gain > 0.0)
  {
    yals->ddfw.uwrvs [yals->ddfw.uwrvs_size] = true_lit;
    yals->ddfw.uwvars_gains [yals->ddfw.uwrvs_size] = flip_gain;
    yals->ddfw.uwrvs_size++;
    if (yals->ddfw.best_weight < flip_gain)
    {
      yals->ddfw.best_var = true_lit;
      yals->ddfw.best_weight = flip_gain;
    }
    yals->ddfw.sum_uwr += flip_gain;
  }
  else if (flip_gain == 0.0) {
    yals->ddfw.non_increasing [yals->ddfw.non_increasing_size++] = true_lit;
  }
}

// outdated, now use a heap
void compute_uwvars_from_unsat_clause (Yals *yals, int cidx)
{
  int * lits = yals_lits (yals, cidx);
  int lit;
  while ((lit = *lits++))
  {
    if (yals->ddfw.helper_hash_vars [abs (lit)] == 0)
    {
      determine_uwvar (yals, abs (lit));
      yals->ddfw.helper_hash_vars [abs (lit)] = 1;
      PUSH (yals->ddfw.helper_hash_changed_idx1, abs(lit));
    }
  }
}

// outdated, now use a heap
void compute_uwvars_from_unsat_clauses2 (Yals *yals)
{
  //double s = yals_time (yals);
  RELEASE (yals->ddfw.helper_hash_changed_idx1);
  Lnk * p;
  if (yals->unsat.usequeue)
  {
    for (p = yals->unsat.queue.first; p; p = p->next)
    {
      compute_uwvars_from_unsat_clause (yals, p->cidx);
      /** IDEA: If number of unsat clasues are large, eg, yals_nunsat (yals) > X
      then check unsat clauses until we have Y uwrvs, eg, yals->ddfw.uwrvs_size>=5 **/
      //if ((double) yals->ddfw.uwrvs_size >10 ) break;
    }
  }
  else
  {
    for (int c = 0; c < COUNT(yals->unsat.stack); c++)
    {
      int cidx = PEEK (yals->unsat.stack, c);
      compute_uwvars_from_unsat_clause (yals, cidx);
      //if (yals_nunsat (yals) > 100 && yals->ddfw.uwrvs_size >= 1) break;
    }
  }
  for (int i=0; i < COUNT(yals->ddfw.helper_hash_changed_idx1); i++)
  {
    int idx = PEEK (yals->ddfw.helper_hash_changed_idx1, i);
    yals->ddfw.helper_hash_vars [idx] = 0;
  }
   //yals->ddfw.compute_uwvars_from_unsat_clauses_time += yals_time (yals) - s;
}

// outdated, now use a heap
void yals_ddfw_compute_uwrvs (Yals * yals)
{
  LOG ("Compute uvars");
  yals->ddfw.best_weight = INT_MIN*1.0;
  yals->ddfw.uwrvs_size = 0;
  yals->ddfw.non_increasing_size = 0;
  yals->ddfw.best_var = 0 ;
  yals->ddfw.sum_uwr = 0;
  

    for (int i=0; i< COUNT(yals->ddfw.uvars); i++)
      determine_uwvar (yals, PEEK (yals->ddfw.uvars, i));

#ifndef NDEBUG
  yals_check_global_weight_invariant (yals);
  yals_check_global_best_weight_invariant (yals);
#endif

}

void yals_ddfw_create_neighborhood_map (Yals *yals)
{
  // nmap = malloc (yals->nclauses* sizeof (ClauseNeighboursDups));
  for (int cidx =0; cidx< yals->nclauses; cidx++)
    compute_neighborhood_for_clause_init (yals, cidx);
  ndone = 1;

  // card_nmap = malloc (yals->card_nclauses* sizeof (ClauseNeighboursDups));
  for (int cidx =0; cidx< yals->card_nclauses; cidx++)
    card_compute_neighborhood_for_clause_init (yals, cidx);
  card_ndone = 1;
}

// compute neighborhood for clause that is a cardinality constraint
void card_compute_neighborhood_for_clause_init (Yals *yals, int cidx)
{    
  // RELEASE (card_nmap [cidx].neighbors);
  RELEASE (yals->ddfw.card_helper_hash_changed_idx);
 
  int lit, occ, neighbor;
  const int * occs, *p;
  int * lits = yals_card_lits (yals, cidx);
  while ((lit = *lits++))
  {
    occs = yals_card_occs (yals, lit);
    //printf ("%d ",lit);
    for (p = occs; (occ = *p) >= 0; p++)
    {
      neighbor = occ >> LENSHIFT;
      //if (!yals_satcnt (yals, neighbor)) continue;
      if (cidx != neighbor && yals->ddfw.card_helper_hash_clauses[neighbor]++ == 0)
      { // if a clause has been seen more than once, do not add it again
        PUSH(yals->ddfw.card_helper_hash_changed_idx, neighbor);
        // PUSH (card_nmap [cidx].neighbors, neighbor);
      }
    }
  }
  for (int k=0; k<COUNT(yals->ddfw.card_helper_hash_changed_idx); k++)
  { // resetting the helper_hash_clauses so all counts are 0 for subsequent calls
    int changed = PEEK (yals->ddfw.card_helper_hash_changed_idx,k);
    yals->ddfw.card_helper_hash_clauses [changed] = 0;
  }
  //printf ("\n nmap %d", COUNT (nmap [cidx].neighbors) );

  //TODO: this list can be freed (helper_hash_clauses)
  //TODO: in general it looks like some memory is never freed after it is used...
}

void compute_neighborhood_for_clause_init (Yals *yals, int cidx)
{    
  // RELEASE (nmap [cidx].neighbors);
  RELEASE (yals->ddfw.helper_hash_changed_idx);
 
  int lit, occ, neighbor;
  const int * occs, *p;
  int * lits = yals_lits (yals, cidx);
  while ((lit = *lits++))
  {
    occs = yals_occs (yals, lit);
    //printf ("%d ",lit);
    for (p = occs; (occ = *p) >= 0; p++)
    {
      neighbor = occ >> LENSHIFT;
      //if (!yals_satcnt (yals, neighbor)) continue;
      if (cidx != neighbor && yals->ddfw.helper_hash_clauses[neighbor]++ == 0)
      {
        PUSH(yals->ddfw.helper_hash_changed_idx, neighbor);
        // PUSH (nmap [cidx].neighbors, neighbor);
      }
    }
  }
  for (int k=0; k<COUNT(yals->ddfw.helper_hash_changed_idx); k++)
  {
    int changed = PEEK (yals->ddfw.helper_hash_changed_idx,k);
    yals->ddfw.helper_hash_clauses [changed] = 0;
  }
  //printf ("\n nmap %d", COUNT (nmap [cidx].neighbors) );
}


void yals_ddfw_init_build (Yals *yals) {
  yals_init_ddfw (yals);
  
   if (!yals->wid && yals->opts.computeneiinit.val)
     yals_ddfw_create_neighborhood_map (yals);
}

void yals_ddfw_update_lit_weights_on_make (Yals * yals, int cidx, int lit) {
  int* lits = yals_lits (yals, cidx), *p;
  int lt;
  int soft = 0;
  double maxs_weight = 1.0;
  if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
      soft = 1;
      if (!yals->opts.maxs_init_weight_relative.val)
        maxs_weight = PEEK (yals->maxs_clause_weights, cidx);
    }
  // sat1_weights [get_pos(lit)] += yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight;
  yals_ddfw_update_var_weight (yals, lit, soft, 1, yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
  for (p = lits; (lt = *p); p++)
  {
    // unsat_weights [get_pos(lt)] -= yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight;
    yals_ddfw_update_var_weight (yals, lt, soft, 0, -yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
    /** var_unsat_count is for quick decision **/
    // yals->ddfw.var_unsat_count [abs (lt)]--;
  }
}

// never called
// void yals_ddfw_card_update_lit_weights_on_make (Yals * yals, int cidx, int lit)
// {
//   //double s = yals_time (yals);
//   yals->ddfw.sat1_weights [get_pos(lit)] += yals->ddfw.ddfw_card_weights [cidx];
//   int* begin, *end;
//   int lt;
//   yals_card_unsat_iters (yals, cidx, &begin, &end);
//   for (; begin != end; begin++) {
//     lt = *begin;
//     yals->ddfw.unsat_weights [get_pos(lt)] -= yals->ddfw.ddfw_card_weights [cidx];
//     /** var_unsat_count is for quick decision **/
//     // yals->ddfw.var_unsat_count [abs (lt)]--;
//   }
// }

void yals_ddfw_update_lit_weights_on_break (Yals * yals, int cidx, int lit) {
  double maxs_weight = 1.0;
  int soft = 0;
  if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
      soft = 1;
      if (!yals->opts.maxs_init_weight_relative.val)
        maxs_weight = PEEK (yals->maxs_clause_weights, cidx);
    }
  // sat1_weights [get_pos(-lit)] -= yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight; // lit no longer critical
  yals_ddfw_update_var_weight (yals, -lit, soft, 1, -yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
  int* lits = yals_lits (yals, cidx), *p;
  int lt;
  for (p = lits; (lt = *p); p++){ // all lits now in unsat clause, contribute to unsat weight
    // unsat_weights [get_pos(lt)] += yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight;
    yals_ddfw_update_var_weight (yals, lt, soft, 0, yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
    /** var_unsat_count is for quick decision **/
    // yals->ddfw.var_unsat_count [abs (lt)]++;
  }
}

// outdated, now use a heap
int yals_pick_literal_ddfw (Yals * yals)
{ 
  /* pick_method=1: selects the variable that reduces unsat weight the most
    pick-method=2 (--wrand): selects an unsat reducing variable with a probability, proportal to its unsat weight reduction value.
  */
  LOG ("Pick literal ddfw");
  if (yals->ddfw.pick_method == 1) 
    return yals->ddfw.best_var;
  else if (yals->ddfw.pick_method == 2) 
  {
      double drand = (double)  yals_rand_mod (yals, INT_MAX-1) / (double) (INT_MAX);
      for (int i=0; i< yals->ddfw.uwrvs_size; i++)
      {
        double gain_ratio = (double) yals->ddfw.uwvars_gains [i] / (double) yals->ddfw.sum_uwr;
        if (gain_ratio >= drand)
          return  yals->ddfw.uwrvs[i];
      }
    return yals->ddfw.best_var;
  } else {
    return 0;
  }


  // random uwrvs selection
  // int pos = yals_rand_mod (yals, yals->ddfw.uwrvs_size);
  // lit = yals->ddfw.uwrvs[pos];
}

int compute_sat_count (Yals *yals, int cidx)
{
    int satcnt = 0, lit;
    int* lits = yals_lits (yals, cidx), *p;
    for (p = lits; (lit = *p); p++) {
      if (!yals_val (yals, lit)) continue;
      satcnt++;
    }
    return satcnt;
}

int yals_pick_non_increasing (Yals * yals)
{
  int lit;
  if(yals->ddfw.non_increasing_size > 0) // this is already ensured before the call in inner_loop_max_tries
  {
    int pos = yals_rand_mod (yals, yals->ddfw.non_increasing_size);
    lit = yals->ddfw.non_increasing[pos];
  }
  else
    lit = yals_pick_literals_random (yals);
  return lit;
}

int yals_pick_literals_random (Yals * yals)
{
  int var = yals_rand_mod (yals, yals->nvars-1)+1;
  int lit = yals_val (yals, var) ? var : -var;
  return lit;
}

void yals_check_lits_weights_sanity_var (Yals *yals, int v)
{
  int val = yals_val (yals, v);
  int tl = val? v : -v;
  int s1w = 0, uw=0, occ;
  const int * occs = yals_occs (yals, tl), *p;
  for (p=occs; (occ = *p) >= 0; p++)
  {
    int cidx = occ >>LENSHIFT;
    if (yals_satcnt (yals, cidx) == 1)
      s1w += yals->ddfw.ddfw_clause_weights [cidx];
  }

  assert (s1w == yals->ddfw.sat1_weights [get_pos(tl)]);
   
  occs = yals_occs (yals, -tl);
   
  for (p=occs; (occ = *p) >= 0; p++)
  {
    int cidx = occ >>LENSHIFT;
    if (!yals_satcnt (yals, cidx))
      uw += yals->ddfw.ddfw_clause_weights [cidx];
  }
  assert (uw == yals->ddfw.unsat_weights [get_pos(-tl)]);
}

void yals_check_lits_weights_sanity (Yals *yals)
{
  for (int v=1; v< yals->nvars; v++)
    yals_check_lits_weights_sanity_var (yals, v);
}

// not used
// void yals_ddfw_update_lit_weights_at_restart_var (Yals *yals, int v)
// {
//   int val = yals_val (yals, v);
//   int tl = val? v : -v;
//   int s1w = 0, uw=0, occ;
//   const int * occs = yals_occs (yals, tl), *p;
//   for (p=occs; (occ = *p) >= 0; p++)
//   {
//     int cidx = occ >>LENSHIFT;
//     if (yals_satcnt (yals, cidx) == 1)
//       s1w += yals->ddfw.ddfw_clause_weights [cidx];
//     if (yals_satcnt (yals, cidx) == 0)
//       uw += yals->ddfw.ddfw_clause_weights [cidx];
//   }


//   yals->ddfw.sat1_weights [get_pos(tl)] = s1w;
//   yals->ddfw.unsat_weights [get_pos (tl)] = uw;

//   s1w = 0;
//   uw = 0;
  
//   occs = yals_occs (yals, -tl);
   
//   for (p=occs; (occ = *p) >= 0; p++)
//   {
//     int cidx = occ >>LENSHIFT;
//     if (!yals_satcnt (yals, cidx))
//       uw += yals->ddfw.ddfw_clause_weights [cidx];
//     if (yals_satcnt (yals, cidx) == 1)
//       s1w += yals->ddfw.ddfw_clause_weights [cidx];
//   }
//   yals->ddfw.sat1_weights [get_pos (-tl)] = s1w;
//   yals->ddfw.unsat_weights [get_pos(-tl)] = uw;
// }

// not used
// void yals_ddfw_update_lit_weights_at_restart (Yals *yals)
// {
//   for (int v=1; v< yals->nvars; v++)
//     yals_ddfw_update_lit_weights_at_restart_var (yals, v);
// }

/*
  
  Initialize the ddfw weight change of variables in clause.

*/
void yals_ddfw_update_lit_weights_at_start (Yals * yals, int cidx, int satcnt, int crit) {
  int* lits = yals_lits (yals, cidx), *p1;
  int lt, soft = 0;
  double maxs_weight = 1.0;
  if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
      soft = 1;
      if (!yals->opts.maxs_init_weight_relative.val)
        maxs_weight = PEEK (yals->maxs_clause_weights, cidx);
  }
  if (!satcnt) {
    for (p1 = lits; (lt = *p1); p1++)
      //  unsat_weights [get_pos (lt)] += yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight;
        yals_ddfw_update_var_weight (yals, lt, soft, 0, yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
  }
  else if (satcnt == 1)
    // sat1_weights [get_pos (crit)] += yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight;
    yals_ddfw_update_var_weight (yals, crit, soft, 1, yals->ddfw.ddfw_clause_weights [cidx] * maxs_weight);
}

/*
  
  Initialize the ddfw weight change of variables in cardinality constraint.

*/
void yals_card_ddfw_update_lit_weights_at_start (Yals * yals, int cidx, int satcnt, int bound) {
  yals_msg (yals, 4, "Starting initial weights for cidx %d", cidx);

  double w = yals_card_get_calculated_weight (yals, cidx);
  double w_add_neg = yals_card_get_calculated_weight_change_neg (yals, cidx);

  yals_msg (yals, 4, "Calculated weight %lf, weight change %lf", w, w_add_neg);
   
  if (satcnt < bound) { // falsified

    yals_card_sat_weight_update (yals, cidx, w_add_neg, 0);

    yals_card_unsat_weight_update (yals, cidx, w, 0);

  } else if (bound == satcnt) { // critically satisfied

    LOGCARDCIDX (cidx, "critical SAT");

    yals_card_sat_weight_update (yals, cidx, w_add_neg, 0);
  } // else: satisfied, not critically satisfied (Do nothing)

  yals_msg (yals, 3, "finished initial weights for cidx %d", cidx);
}

int yals_nunsat_external (Yals *yals)
{
  return yals_nunsat (yals);
}

int yals_flip_count (Yals *yals)
{
  return yals->stats.flips;
}

void yals_print_stats (Yals * yals)
{
  // double avg_len_consecutive_lm = (double) (yals->ddfw.consecutive_lm_length) / (double) (yals->ddfw.count_conscutive_lm);
  //  (double) (yals->ddfw.count_conscutive_lm);
  // printf ("c stats | %d %d %d %d %d %d %d %d %f %d %d %d %d %d %d %d %f ", yals->ddfw.pick_method, yals->stats.flips, yals->ddfw.local_minima,   yals->ddfw.wt_count
  //                 , yals->ddfw.missed_guaranteed_uwvars, yals->ddfw.sideways,
  //                 yals->ddfw.consecutive_lm_length, yals->ddfw.count_conscutive_lm,  avg_len_consecutive_lm, yals->ddfw.max_consecutive_lm_length, yals_nunsat (yals),     
  //                 yals_minimum (yals), yals->ddfw.alg_switch, yals->stats.restart.inner.count, 
  //                 yals->fres_fact, yals->fres_count, yals->stats.time.restart);
  // double r = (double) yals->ddfw.source_not_selected / (double) yals->ddfw.total_transfers;
  //printf ("c stats |%ld ", yals->stats.flips);
}

/*------------------------------------------------------------------------*/
/* Report the average DDFW weight of constraints grouped by length, for    */
/* clauses and cardinality constraints separately. Printed once when the   */
/* solver ends. For palsat, call this on the winning thread's Yals.        */
/*------------------------------------------------------------------------*/
void yals_print_length_weights (Yals * yals)
{
  int i, len, maxlen;
  int * cnt;
  double * sum;
  const int * p;

  // ---- clauses (length = number of literals) ----
  maxlen = 0;
  for (i = 0; i < yals->nclauses; i++) {
    len = 0;
    for (p = yals_lits (yals, i); *p; p++) len++;
    if (len > maxlen) maxlen = len;
  }
  if (yals->nclauses > 0) {
    NEWN (cnt, maxlen + 1);
    NEWN (sum, maxlen + 1);
    for (len = 0; len <= maxlen; len++) { cnt[len] = 0; sum[len] = 0.0; }
    for (i = 0; i < yals->nclauses; i++) {
      len = 0;
      for (p = yals_lits (yals, i); *p; p++) len++;
      cnt[len]++;
      sum[len] += yals->ddfw.ddfw_clause_weights[i];
    }
    for (len = 0; len <= maxlen; len++)
      if (cnt[len])
        yals_msg (yals, 0,
          "avg ddfw weight, clause length %d: %.4f over %d clauses",
          len, sum[len] / (double) cnt[len], cnt[len]);
    DELN (cnt, maxlen + 1);
    DELN (sum, maxlen + 1);
  }

  // ---- cardinality constraints (length = number of literals) ----
  maxlen = 0;
  for (i = 0; i < yals->card_nclauses; i++) {
    len = yals_card_length (yals, i);
    if (len > maxlen) maxlen = len;
  }
  if (yals->card_nclauses > 0) {
    NEWN (cnt, maxlen + 1);
    NEWN (sum, maxlen + 1);
    for (len = 0; len <= maxlen; len++) { cnt[len] = 0; sum[len] = 0.0; }
    for (i = 0; i < yals->card_nclauses; i++) {
      len = yals_card_length (yals, i);
      cnt[len]++;
      sum[len] += yals->ddfw.ddfw_card_weights[i];
    }
    for (len = 0; len <= maxlen; len++)
      if (cnt[len])
        yals_msg (yals, 0,
          "avg ddfw weight, card length %d: %.4f over %d cardinality constraints",
          len, sum[len] / (double) cnt[len], cnt[len]);
    DELN (cnt, maxlen + 1);
    DELN (sum, maxlen + 1);
  }
}

/*

  Note: uvars does not contain only falsified literals
  the reason for this is that cardinality constraints
  may contain both falsified and satisfied literals 
  while still being falsified. We would not want to 
  update uvars on every flip for every cardinality 
  constraint. So, we overpopulate uvars. This cannot
  lead to flipping a literal not contained in a 
  falsified constraint because the weight would be 
  negative.

*/
void yals_add_a_var_to_uvars (Yals * yals , int lit, int soft)
{
  int * var_unsat_count, * uvar_pos;
  STACK_INT *uvars;
  int var = ABS (lit);
  if (yals->using_maxs_weights && soft) {
    var_unsat_count = yals->ddfw.var_unsat_count_soft;
    uvar_pos = yals->ddfw.uvar_pos_soft;
    uvars = &yals->ddfw.uvars_soft;
  }
  else {
    var_unsat_count = yals->ddfw.var_unsat_count;
    uvar_pos = yals->ddfw.uvar_pos;
    uvars = &yals->ddfw.uvars;
  }
  
  var_unsat_count [var]++;
  if (uvar_pos [var] == -1)
  {
    PUSH (*uvars, var);
    uvar_pos [var] = COUNT (*uvars) - 1;
  }
}

void yals_remove_a_var_from_uvars (Yals * yals , int lit, int soft)
{
  int * var_unsat_count, * uvar_pos;
  STACK_INT *uvars;
  int var = ABS (lit);
  if (yals->using_maxs_weights && soft) {
    var_unsat_count = yals->ddfw.var_unsat_count_soft;
    uvar_pos = yals->ddfw.uvar_pos_soft;
    uvars = &yals->ddfw.uvars_soft;
  }
  else {
    var_unsat_count = yals->ddfw.var_unsat_count;
    uvar_pos = yals->ddfw.uvar_pos;
    uvars = &yals->ddfw.uvars;
  }

  var_unsat_count [var]--;
  LOG ("var unsat count %d %d", var, var_unsat_count [var] );
  assert (var_unsat_count [var] >= 0);
  if (uvar_pos [var] > -1 && !var_unsat_count [var])
  {
    int remove_pos = uvar_pos [var];
    int top_element = TOP (*uvars);
    POKE (*uvars, remove_pos, top_element);
    uvar_pos [top_element] = remove_pos;
    POP (*uvars);
    uvar_pos [var] = -1;
  }
}

void yals_add_vars_to_uvars (Yals* yals, int cidx, int constraint_type) {
  int * lits = NULL;
  int lit;
  int soft = 0;
  if (constraint_type == TYPECLAUSE) {
    lits = yals_lits (yals, cidx);
    if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) 
      soft = 1;
  } else if (constraint_type == TYPECARDINALITY) {
    lits = yals_card_lits (yals, cidx);
    if (yals->using_maxs_weights && !yals->hard_card_ids[cidx]) 
      soft = 1;
  }
  
  while ((lit=*lits++)) {
    if (!yals_val (yals, lit))
      yals_add_a_var_to_uvars (yals, abs(lit), soft);
  }
}


// NEVER CALLED
// int yals_var_in_unsat (Yals *yals, int v)
// {
//   int * pos_oocs = yals_occs (yals, v);
//   const int *o;
//   int occ;
//   for (o = pos_oocs; (occ = *o) >= 0; o++)
//   {
//     int pcidx = occ >> LENSHIFT;
//     if (!yals_satcnt (yals, pcidx))
//       return 1;
//   }

//   int * neg_occs = yals_occs (yals, -v);
//   for (o = neg_occs; (occ = *o) >= 0; o++)
//   {
//     int ncidx = occ >> LENSHIFT;
//     if (!yals_satcnt (yals, ncidx))
//       return 1;
//   }
//   return 0;
// }

void yals_delete_vars_from_uvars (Yals* yals, int cidx, int constraint_type) {
  int * lits = NULL;
  int lit;

  int soft = 0;
  if (constraint_type == TYPECLAUSE) {
    lits = yals_lits (yals, cidx);
    if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) 
      soft = 1;
  } else if (constraint_type == TYPECARDINALITY) {
    lits = yals_card_lits (yals, cidx);
    if (yals->using_maxs_weights && !yals->hard_card_ids[cidx]) 
      soft = 1;
  }

  while ((lit=*lits++))
  {
    if (!yals_val (yals, lit)) {
      yals_remove_a_var_from_uvars (yals, lit, soft);
    }
  }
}

int yals_inner_loop_max_tries (Yals * yals)
{
  LOG ("Inner loop max tries with %d cutoff", yals->opts.cutoff.val);
  int lit = 0;
  for (int t=0; t<yals->opts.maxtries.val; t++)
  {
    if (!yals_nunsat(yals))
      return 1;
    yals_restart_inner (yals);
    for (int c=0; c<yals->opts.cutoff.val || (yals->opts.cutoff.val <= 0) ; ++c)// cutoff 0 is unlimited flips
    {
       if (!yals_nunsat(yals))
        return 1;
       // Check external termination callback (e.g., palsat sibling worker won).
       // Throttle: only call the callback every termint iterations.
       if (yals->cbs.term.fun && yals->limits.term-- <= 0) {
         yals->limits.term = yals->opts.termint.val;
         if (yals->cbs.term.fun (yals->cbs.term.state)) {
           yals_msg (yals, 1, "forced to terminate (max_tries loop)");
           return -1;
         }
       }
          double start = yals_time (yals);
          lit = yals_pick_literal_from_heap (yals, 0);
          yals->stats.maxs_time.var_selection += yals_time (yals) - start;
          // may add sideways flips here
          if (lit) {
            LOG ("picking from ddfw heap");
          }
          else {
            yals_ddfw_transfer_weights (yals);
            c--;
            yals_check_global_satisfaction_invariant (yals);
            continue;
          }
          yals_flip_ddfw (yals, lit);
    }
  }
  return -1;    
}

void yals_set_wid (Yals * yals, int widx)
{
  // Worker identity is fundamental (e.g. the shared cache keys on it), so set
  // it unconditionally rather than gating on an optional feature.
  yals->wid = widx;
}


 
/*

Additional functions for cardinality constraint handling

*/
void yals_new_cardinality_constraint (Yals * yals) {
  int len = COUNT (yals->clause), * p, lit;
  int bound = yals->bound;
  if (!len) {
    LOG ("found empty clause in original formula");
    yals->mt = 1;
  }
  if (len < bound) {
    LOG ("found trivially unsat cardinality constraint");
    yals_abort (yals, "added trivially unsat cardinality constraint");
  }
  if (len == bound) {
    LOG ("found unit cardinality constraint");
    // soft units are not assigned
    if (!yals->using_maxs_weights || yals->parsed_weight != yals->maxs_hard_weight)
      for (p = yals->clause.start; p < yals->clause.top; p++) {
        lit = *p;
        LOG ("found unit clause %d in original formula", lit);
        PUSH (yals->trail, lit);
      }    
  }
  PUSH (yals->card_cdb, bound);
  for (p = yals->clause.start; p < yals->clause.top; p++) {
    lit = *p;
    PUSH (yals->card_cdb, lit);
  }
  PUSH (yals->card_cdb, 0);
  LOGLITS (yals->card_cdb.top - len - 2, "new length %d", len+1);
  if (yals->using_maxs_weights) {
    PUSH (yals->maxs_card_weights, yals->parsed_weight);
    if (yals->parsed_weight != yals->maxs_hard_weight)
      yals->maxs_acc_hard_weight += yals->parsed_weight;
  }
}

void yals_set_max_weight (Yals * yals, double weight) {
  assert (weight >= 0);
  yals->maxs_hard_weight = weight;
  yals->maxs_acc_hard_weight = 0;
}

void yals_using_maxs (Yals * yals, int is_using) {
  yals->using_maxs_weights = is_using;
  if (is_using) {
    yals->is_pure = 1;
    yals->cardinality_is_hard = 1;
  }
  else {
    yals->is_pure = 0;
    yals->cardinality_is_hard = 0;
  }
  yals->hard_polarity = 0;
  yals->weight_transfer_soft = 0;
}

void yals_card_add_weight (Yals * yals, double weight) {
  assert (weight >= 0);
  yals->parsed_weight = weight;
}

void yals_card_add (Yals * yals, int lit, int is_bound) {
  if (is_bound) {
    assert(lit >= 1);
    yals->bound = lit; // set the bound for the cardinality constaint currently being added
  } else {
    if (lit) { // adding a lit to the cardinality constraint
      // ignore trivial marking for cardinality constraints
      // signed char mark;
      int idx;
      if (lit == INT_MIN)
        yals_abort (yals, "can not add 'INT_MIN' as literal");
      idx = ABS (lit);
      if (idx == INT_MAX)
        yals_abort (yals, "can not add 'INT_MAX' as literal");
      if (idx >= yals->nvars) yals->nvars = idx + 1;
      PUSH (yals->clause, lit);

      // check if formula is pure on each lit parsed
      if (yals->using_maxs_weights) {
        int polarity = ABS (lit) / lit;
        if (yals->maxs_hard_weight == yals->parsed_weight) {
          if (yals->hard_polarity == 0) {
            yals->hard_polarity = polarity;
          } else if (yals->hard_polarity != polarity) 
            yals->is_pure = 0;
        } else {
          yals->cardinality_is_hard = 0;
          if (yals->hard_polarity == polarity) 
            yals->is_pure = 0;
        }
      }


    } else { // finished adding cardinality constraint
      yals_new_cardinality_constraint (yals);
      CLEAR (yals->clause);
    }
  }
}

/*
MaxSat helper functions
*/

// weighted selection of variable from lit_scores
int yals_pick_from_list_scores (Yals * yals) {
  
  int counter = 0, res;
  double sum,lim,score = 0;
  int choice_of = COUNT (yals->lit_scores);

  assert (choice_of > 0);

  sum = 0;
  for (int i = 0; i < choice_of; i++) {
    sum += PEEK (yals->lit_scores, i).score;
    assert (PEEK (yals->lit_scores, i).score >= 0);
  }

  lim = (yals_rand (yals) / (1.0 + (double) UINT_MAX))*sum;

  res = PEEK (yals->lit_scores, 0).lit;
  score = PEEK (yals->lit_scores, 0).score;

  if (sum > 0.0) {

    while (counter+1 < choice_of && score <= lim) {
      lim -= score;
      counter++;
      res = PEEK (yals->lit_scores, counter).lit;
      score = PEEK (yals->lit_scores, counter).score;
    }

  }

  yals->ddfw.best_weight = score;

  return res;
}




/*
  Control for maxsat outer loop
*/
void yals_maxs_outer_loop (Yals * yals) {
  
  assert (yals->using_maxs_weights);

  if (!yals->opts.maxtries.val) yals->opts.maxtries.val = 1;
  if (!yals->opts.cutoff.val && yals->limits.flips) yals->opts.cutoff.val = yals->limits.flips;

  yals->maxs_hard_offset = 0;

  if (yals->is_pure) {
    yals_msg (yals, 1, "Entering Pure MaxSAT inner loop");
    yals->ddfw.uvars_heap.score_fun = yals_pure_hard_score;
    yals->ddfw.uvars_heap_soft.score_fun = yals_pure_soft_score;
    if (yals->opts.init_solution.val)
      yals_init_assignment_parse (yals);
    else
      yals_init_assignment_pure (yals);
    yals_pure_maxs_inner_loop (yals);
  } else if (yals->opts.init_solution.val) {
    yals_msg (yals, 1, "Entering MaxSAT inner loop");
    yals_msg (yals, 1, "WARNING: MaxSAT algorithm incomplete, NO guarantees");
    yals->ddfw.uvars_heap.score_fun = yals_batt_score;
    if (yals->opts.init_solution.val)
      yals_init_assignment_parse (yals);
    else
      yals_init_assignment_random (yals);
    yals_ass_maxs_inner_loop (yals);
  }
}