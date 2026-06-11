/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _maxsat_h_INCLUDED
#define _maxsat_h_INCLUDED

#include "yals.h"
#include "yils_card.h"
#include "invariants.h"
#include "stack.h"
#include <ctype.h>
#include <limits.h>

/*

******

General MaxSAT has not been properly implemented yet.

******

  Implements the API for MaxSAT problems.

  - Variable scores, used to sort variables on the variable heap
  to determine which vairable has the best ddfw weight change.

  - Initialization schemes for generating an initial solution.

  - Inner and outer restarts.

  - Inner loop for solving.

  - Storing best cost solution and displaying improvements. (Also used for Pure MaxSAT)

*/




void yals_maxs_report (Yals * yals, const char * fmt, ...) {
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
    " : nunsat best %d (tmp %d), clauses %d, constraints %d, flips %.0f, %.2f sec, %.2f kflips/sec\n",
    yals->stats.best, yals->stats.tmp,yals->stats.best_clauses, yals->stats.best_cardinality, f, t, yals_avg (f/1e3, t));
  fprintf (yals->out,
    "c   weights best %lf (tmp %lf), clauses %lf, constraints %lf\n",
    yals->stats.maxs_best_cost, yals->stats.maxs_tmp_weight,yals->stats.maxs_clause_best_weight, yals->stats.maxs_card_best_weight);
  fprintf (yals->out,
    "c   soft clauses %d, constraints %d\n",
    yals->stats.best_clauses, yals->stats.best_cardinality);
  fprintf (yals->out,
    "c   offset %lf, sum %lf\n",
    yals->propagated_soft_weight, yals->propagated_soft_weight + yals->stats.maxs_best_cost);
  fflush (yals->out);
  yals_msgunlock (yals);
}

// valid assignment if 0 hard constrants are falsified
static int yals_valid_maxs_assignment (Yals * yals) {
  return (!yals_nunsat (yals));
}

double yals_get_soft_cost (Yals * yals) {

  return (yals->unsat_soft.maxs_weight + yals->card_unsat_soft.maxs_weight);
}

double yals_get_cost (Yals * yals) {
  if (!yals_valid_maxs_assignment (yals)) return YALS_DOUBLE_MAX;

  return (yals->unsat_soft.maxs_weight + yals->card_unsat_soft.maxs_weight);
}

static double yals_soft_cost_of_flip (Yals * yals, int lit) {
  double original_cost = yals_get_soft_cost (yals);
  double change_in_cost = 0.0;

  // remove cost of made soft constraints
  const int * p, * occs;
  int bound, occ;
  occs = yals_occs (yals, lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    int cidx = occ >> LENSHIFT;
    if (yals->f->hard_clause_ids[cidx]) continue;
    if (yals_satcnt (yals, cidx) == 0) {// made
      change_in_cost -= PEEK (yals->maxs_clause_weights, cidx);
    }
  }
  occs = yals_card_occs (yals, lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    int cidx = occ >> LENSHIFT;
    if (yals->f->hard_card_ids[cidx]) continue;
    bound = yals_card_bound (yals, cidx);
    if (bound - yals_card_satcnt (yals, cidx) == -1) {// made
      change_in_cost -= PEEK (yals->maxs_card_weights, cidx);
    }
  }

  // add cost of broken soft constraints
  occs = yals_occs (yals, -lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    int cidx = occ >> LENSHIFT;
    if (yals->f->hard_clause_ids[cidx]) continue;
    if (yals_satcnt (yals, cidx) == 1) {// broken
      change_in_cost += PEEK (yals->maxs_clause_weights, cidx);
    }
  }
  occs = yals_card_occs (yals, -lit);
  for (p = occs; (occ = *p) >= 0; p++) {
    int cidx = occ >> LENSHIFT;
    if (yals->f->hard_card_ids[cidx]) continue;
    bound = yals_card_bound (yals, cidx);
    if (bound - yals_card_satcnt (yals, cidx) == 0) {// broken
      change_in_cost += PEEK (yals->maxs_card_weights, cidx);
    }
  }

  yals_msg (yals, 2, "Original Cost %lf best cost %lf change %lf new cost %lf", original_cost, yals->stats.maxs_best_cost, change_in_cost, original_cost + change_in_cost);

  return original_cost + change_in_cost;
}

void yals_satisfy_trivial_soft (Yals * yals) {
  
  int flipped = 1;

  yals_msg (yals, 2, "Start flipping trivial soft constraints");

  while (flipped) {
    flipped = 0;
    for (int i=0; i< COUNT(yals->ddfw.uvars_soft); i++) {
      if (yals_polarity (yals, PEEK (yals->ddfw.uvars_soft, i)) != yals->hard_polarity) continue;
      if (yals_pure_soft_score (yals, PEEK (yals->ddfw.uvars_soft, i)) == YALS_DOUBLE_MAX) {
        int var = PEEK (yals->ddfw.uvars_soft, i);
        int lit = yals_val (yals, var) ? var : -var;
        yals_flip_ddfw (yals, lit);
        flipped = 1;

        // need if statement here because heap updated lazily (right before lit selection...)
        // if (yals_heap_contains (&yals->ddfw.uvars_heap_soft, ABS (lit)))
        break;
      }
    }
  }
  yals_msg (yals, 2, "End flipping trivial soft constraints");
}

void yals_save_new_minimum_cost (Yals * yals) {
  int nunsat = yals_nunsat (yals);

  double cost_unsat = yals_get_cost (yals);
  int hard_unsat = yals_hard_unsat (yals);
  int soft_unsat = yals_soft_unsat (yals);

  yals_msg (yals, 4, "hard unsat %d soft unsat %d cost unsat %lf", hard_unsat,soft_unsat, cost_unsat);
  yals_msg (yals, 4, "hard clause %d soft clause %d hard card %d soft card %d", yals_clause_hard_unsat (yals),yals_clause_soft_unsat (yals),yals_card_hard_unsat (yals),yals_card_soft_unsat (yals) );

  size_t bytes = yals->nvarwords * sizeof (Word);

  if (yals->stats.maxs_worst_cost < cost_unsat && !hard_unsat) yals->stats.maxs_worst_cost = cost_unsat;
  if (yals->stats.maxs_tmp_weight > cost_unsat) { // update of tmp best cost
    LOG ("minimum cost %lf is best assignment w.r.t. nunsat since last restart",cost_unsat);
    yals->stats.maxs_tmp_weight = cost_unsat;
    memcpy (yals->tmp, yals->vals, bytes);
  }


  if (yals->stats.worst < nunsat) yals->stats.worst = nunsat;
  if (yals->stats.tmp > nunsat) {
    LOG ("minimum nunsat %d is best assignment since last restart", nunsat);
    yals->stats.tmp = nunsat;
  }

  if (yals->stats.maxs_best_cost < cost_unsat) return;
  if (yals->stats.maxs_best_cost == cost_unsat) {
    LOG ("minimum cost %lf matches previous overall best assignment", cost_unsat);
    yals->stats.hits++;
    return;
  }


  // if (yals->stats.best == nunsat) {
  // }
  if (hard_unsat < yals->stats.maxs_best_hard_cnt) {
    LOG ("Best hard count %d", hard_unsat);
    yals->stats.maxs_best_hard_cnt = hard_unsat;
    LOG ("hard unsat %d soft unsat %d cost unsat %lf", hard_unsat,soft_unsat, cost_unsat);
    LOG ("hard clause %d soft clause %d hard card %d soft card %d", yals_clause_hard_unsat (yals),yals_clause_soft_unsat (yals),yals_card_hard_unsat (yals),yals_card_soft_unsat (yals) );
    memcpy (yals->best, yals->vals, bytes);
  }
  if (!hard_unsat) {
    LOG ("No falsified hard constraints with new best overall assignment");
    if (nunsat < yals->stats.best) 
      yals->stats.best = nunsat;

    yals->stats.maxs_best_cost = cost_unsat;

    // TODO: decide if this is the stats we want
    yals->stats.best_clauses = yals_clause_soft_unsat (yals);
    yals->stats.best_cardinality = yals_card_soft_unsat (yals);
    yals->stats.hits = 1;

    // handle hard constraints differently if they are going up?
    assert (yals->stats.maxs_best_hard_cnt >= hard_unsat);
    yals->stats.maxs_best_hard_cnt = hard_unsat;
    yals->stats.maxs_clause_best_hard_cnt = yals_clause_hard_unsat (yals);
    yals->stats.maxs_card_best_hard_cnt = yals_card_hard_unsat (yals);

    yals->stats.maxs_clause_best_weight = yals_clause_weight_unsat (yals);
    yals->stats.maxs_card_best_weight = yals_card_weight_unsat (yals);

    memcpy (yals->best, yals->vals, bytes);
    if (yals->opts.verbose.val >= 2 ||
        (yals->opts.verbose.val >= 1 && nunsat <= yals->limits.report.min/2)) {
      yals_maxs_report (yals, "new minimum");
      yals->limits.report.min = nunsat;
    }
  }
}

void yals_update_minimum_cost (Yals * yals) {
  yals_save_new_minimum_cost (yals);
  LOG ("now %d hard clauses unsatisfied", yals_nunsat (yals));
  yals_maxs_check_global_satisfaction_invariant (yals);
}


void yals_init_assignment_parse (Yals *yals) {
  int ch, sign, lit;
  FILE * file;
  double start = yals_time_phase (yals);

  if (!(file = fopen ("init.sol", "r"))) {
    printf ("can not read init.sol");
    exit (1);
  }

BODY:
  ch = getc (file);
  if (ch == EOF) {goto DONE;}
  if (ch == 'v' ||ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n') goto BODY;
  if (ch == '-') {
    ch = getc (file);
    if (ch == '0') {
      printf ("expected non-zero digit");
      exit (1);
    } 
    sign = -1;
  } else sign = 1;
  if (!isdigit (ch)) {
    printf ("expected digit");
  }
  lit = ch - '0';
  while (isdigit (ch = getc (file)))
    lit = 10*lit + (ch - '0');
  if (((lit) >> LD_BITS_PER_WORD) >= (yals->nvarwords)) goto BODY; // extension variables printed in assignment?
  if (sign == 1) SETBIT (yals->vals, yals->nvarwords, lit);
  else CLRBIT (yals->vals, yals->nvarwords, lit);
  goto BODY;
DONE:
  yals_update_sat_and_unsat (yals);

  yals->stats.tmp = INT_MAX;
  yals->stats.maxs_tmp_weight = YALS_DOUBLE_MAX;
  yals_save_new_minimum_cost (yals);
  yals->stats.last = yals_nunsat (yals);
  yals->stats.maxs_last = yals->stats.maxs_best_cost;

  yals->stats.maxs_time.initialization += yals_time_phase (yals) - start;

  yals_maxs_check_global_satisfaction_invariant (yals);
  yals_maxs_check_global_weight_invariant (yals);
}

void yals_init_assignment_random (Yals *yals) {
  int i;
  double start = yals_time_phase (yals);

  for (i = 0; i < yals->nvarwords; i++)
      yals->vals[i] = yals_rand (yals);
  yals_remove_trailing_bits (yals);
  yals_set_units (yals);
  
  yals_update_sat_and_unsat (yals);

  yals->stats.tmp = INT_MAX;
  yals->stats.maxs_tmp_weight = YALS_DOUBLE_MAX;
  yals_save_new_minimum_cost (yals);
  yals->stats.last = yals_nunsat (yals);
  yals->stats.maxs_last = yals->stats.maxs_best_cost;

  yals->stats.maxs_time.initialization += yals_time_phase (yals) - start;

  yals_maxs_check_global_satisfaction_invariant (yals);
  yals_maxs_check_global_weight_invariant (yals);
}




double yals_batt_soft_score (Yals * yals, int var) {
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;

  // TDOD: technically won't have any hard_sat1 weights here, since it is pure
  double hard_flip_loss =
        yals->ddfw.unsat_weights [get_pos (false_lit)]  
        - yals->ddfw.sat1_weights [get_pos (true_lit)];
  double soft_flip_gain =
        yals->ddfw.unsat_weights_soft [get_pos (false_lit)]  
        - yals->ddfw.sat1_weights_soft [get_pos (true_lit)];
  LOG ("determine soft uwvar %d with soft gain %lf and hard loss %lf", var, soft_flip_gain, hard_flip_loss);

  if (hard_flip_loss == 0.0) return YALS_DOUBLE_MAX; // free flip
  return soft_flip_gain / (fabs (hard_flip_loss) + yals->opts.maxs_soft_eps.val);
}

double yals_batt_hard_score (Yals * yals, int var) {
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;

  // TDOD: technically won't have any hard_sat1 weights here, since it is pure
  double hard_flip_gain =
        yals->ddfw.unsat_weights [get_pos (false_lit)]  
        - yals->ddfw.sat1_weights [get_pos (true_lit)];
  double soft_flip_loss =
        yals->ddfw.unsat_weights_soft [get_pos (false_lit)]  
        - yals->ddfw.sat1_weights_soft [get_pos (true_lit)];
  LOG ("determine hard uwvar %d with hard gain %lf and soft loss %lf", var, hard_flip_gain, soft_flip_loss);
  
  if (soft_flip_loss == 0.0) return YALS_DOUBLE_MAX; // free flip
  return hard_flip_gain / (fabs (soft_flip_loss) + yals->opts.maxs_hard_eps.val);
}

double yals_batt_score (Yals * yals, int var) {
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;
  int offset = yals->maxs_hard_offset;

  // TDOD: technically won't have any hard_sat1 weights here, since it is pure
  double hard_flip_gain = yals->ddfw.unsat_weights [get_pos (false_lit)]  - yals->ddfw.sat1_weights [get_pos (true_lit)];
  double soft_flip_gain = yals->ddfw.unsat_weights_soft [get_pos (false_lit)] - yals->ddfw.sat1_weights_soft [get_pos (true_lit)];
  LOG ("determine hard uwvar %d with hard gain %lf and soft loss %lf", var, hard_flip_gain, soft_flip_gain);
  
  return offset * hard_flip_gain + soft_flip_gain;

  // if (soft_flip_loss == 0.0) return YALS_DOUBLE_MAX; // free flip
}

int yals_ass_maxs_inner_loop (Yals * yals) {
  LOG ("Pure MaxSAT inner loop with %d max tries with %d cutoff", yals->opts.maxtries.val,yals->opts.cutoff.val);
  int lit = 0, c = 0;
  int inner_flips, inner_bound;
  inner_flips = 0;

  inner_bound = 10;

  for (int t=0; t<yals->opts.maxtries.val; t++)
  {
    if (!yals_get_cost (yals))
      return 1;
    while ( c<yals->opts.cutoff.val || (yals->opts.cutoff.val <= 0)) // cutoff 0 is unlimited flips
    {

      if (!yals_nunsat(yals)) {
        yals_satisfy_trivial_soft (yals);
        yals_save_new_minimum_cost (yals);
        if (!yals_get_cost (yals)) // 0 cost solution, all soft satisfied
          return 1;
        inner_flips = 0;
        yals->maxs_hard_offset = 0;
        yals_update_score_function_weights (yals);
      }
      else if (inner_flips > inner_bound) {
        yals->maxs_hard_offset += 1;
        yals_update_score_function_weights (yals);
        inner_flips = 0;
        yals_transfer_weights (yals);
      }

      lit = yals_pick_literal_from_heap (yals, 0);
      if (lit) {
        yals_flip_ddfw (yals, lit);
        c++;
      } else {
        yals_transfer_weights (yals);
      }
      inner_flips++;

      if (0) {
        int hard_unsat = yals_hard_unsat (yals);
        int soft_unsat = yals_soft_unsat (yals);

        yals_msg (yals, 1, "hard unsat %d soft unsat %d flipped %d flips %d", hard_unsat,soft_unsat, lit, yals->stats.flips);
      }

    } 
    c = 0;
    // Check if new best assignment
    if (!yals_nunsat(yals)) {
      yals_satisfy_trivial_soft (yals);
      yals_save_new_minimum_cost (yals);
      if (!yals_get_cost (yals)) // 0 cost solution, all soft satisfied
        return 1;
    }
  }


  return -1;    
}


#endif
