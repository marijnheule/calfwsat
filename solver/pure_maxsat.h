/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _pure_maxsat_h_INCLUDED
#define _pure_maxsat_h_INCLUDED

#include "yals.h"
#include "yils_card.h"
#include "invariants.h"
#include "stack.h"
#include "maxsat.h"
#include <limits.h>

/*

  Implements the API for Pure MaxSAT problems.

  - Variable scores, used to sort variables on the variable heap
  to determine which vairable has the best ddfw weight change.

  - Initialization schemes for generating an initial solution.

  - Inner and outer restarts.

  - Inner loop for solving.

*/


double yals_pure_soft_score (Yals * yals, int var) {
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;

  assert (yals_polarity (yals, var) == yals->hard_polarity);

  double hard_flip_loss = yals->ddfw.sat1_weights [get_pos (true_lit)];
  double soft_flip_gain = yals->ddfw.unsat_weights_soft [get_pos (false_lit)];

  LOG ("determine soft uwvar %d with soft gain %lf and hard loss %lf", var, soft_flip_gain, hard_flip_loss);
  
  assert (yals->ddfw.var_unsat_count_soft[var] > 0);
  assert (yals->ddfw.uvar_pos_soft[var] >= 0);
  assert (soft_flip_gain > 0);

  if (hard_flip_loss == 0.0) return YALS_DOUBLE_MAX; // free flip
  return soft_flip_gain / (fabs (hard_flip_loss) + yals->opts.maxs_soft_eps.val);
}

double yals_pure_hard_score (Yals * yals, int var) {
  int true_lit = yals_val (yals, var) ? var : -var;
  int false_lit = -true_lit;

  assert (yals_polarity (yals, var) != yals->hard_polarity);

  double hard_flip_gain = yals->ddfw.unsat_weights [get_pos (false_lit)] ;
  double soft_flip_loss = yals->ddfw.sat1_weights_soft [get_pos (true_lit)];

  LOG ("determine hard uwvar %d with hard gain %lf and soft loss %lf", var, hard_flip_gain, soft_flip_loss);

  assert (yals->ddfw.var_unsat_count[var] > 0);
  assert (yals->ddfw.uvar_pos[var] >= 0);
  assert (hard_flip_gain > 0);
  
  if (soft_flip_loss == 0.0) return YALS_DOUBLE_MAX; // free flip
  return hard_flip_gain / (fabs (soft_flip_loss) + yals->opts.maxs_hard_eps.val);
}

/*
MaxSat initialization schemes

  Pure focused (LinearLS, CarlSAT)
   phase 1. set all variables from soft constraints
   phase 2. make all broken hard constraints 
      (variable selection within each constraint based on a variable score)

  Decimation (SatLIKE, LS-ECNF)
    until all variable are assigned
      propagate hard constraints
      else, propagate soft constraints
      else, assign random variable to a random polarity

  Random
    - When using a pure instance, it may take a while to satisfy hard constraints
    - i.e., flipping enough variables to match polarity of hard constraints
*/

/*
  function for flipping literals in hard constraints on assignment initialization
*/
static void yals_flip_on_init (Yals * yals, int lit) {
  yals->stats.unsum += yals_nunsat (yals);
  yals_flip_value_of_lit (yals, lit);
  yals_make_clauses_after_flipping_lit (yals, lit);
  yals_break_clauses_after_flipping_lit (yals, lit);
  yals_update_minimum_cost (yals);
  yals->last_flip_unsat_count = yals_nunsat (yals);

  yals_update_changed_var_weights (yals);
}

/*
  score for initially flipping literals in hard constraints to satisfy them
*/
static double yals_get_score_on_init (Yals * yals, int lit) {
  return yals_pure_hard_score (yals, lit);
}

/*
  return falsified literal with the best score
*/
static int yals_best_lit_on_init (Yals * yals, int cidx, int constraint_type ) {
  int *lits = NULL, *p, lit, best_lit;
  double score, best_score = -YALS_DOUBLE_MAX;
  best_lit = 0;

  if (constraint_type == TYPECLAUSE) lits = yals_lits (yals, cidx);
  else if (constraint_type == TYPECARDINALITY) lits = yals_card_lits (yals, cidx);

  for (p = lits; (lit = *p); p++ ) {
    if (yals_val (yals, lit)) continue; // already sat lit
    score = yals_get_score_on_init (yals, lit);
    if (score > best_score) {
      best_score = score;
      best_lit = lit;
    }
  }

  assert (best_lit);
  LOG ("Best lit on init %d with best score %lf",best_lit, best_score);
  return best_lit;
}

/*
  hard_polarity = 1 if hard constraints have positive literals
  hard_polarity = 0 if hard constraints have negative literals

  Follow structure of yals_restart_inner for how to wrap this function.
  The function takes the place of 
    
    yals_pick_assignment ()
    yals_update_sat_and_unsat ()
    yals->stats.tmp = INT_MAX;
    yals->stats.maxs_tmp_weight = YALS_DOUBLE_MAX;
    yals_save_new_minimum (yals);
*/
void yals_init_assignment_pure (Yals *yals) {
  int hard_polarity = yals->hard_polarity;
  double start = yals_time_phase (yals);
  int lit;
  int * lits, * p;
  size_t bytes = yals->nvarwords * sizeof (Word);

  assert (yals->using_maxs_weights);

  // initialize assignment to hard constraint polarity
  if (hard_polarity) { // all positive assignment
    memset (yals->vals, 0xff, bytes);
  } else { // all negative assignment
    memset (yals->vals, 0, bytes);
  }

  yals_msg (yals, 1, "Phase 1 : assigning literals from soft constraints");
  LOG ("Phase 1: assigning literals from soft constraints");
  // Phase 1
  //  init assignment to polarity of hard constraints
  //  set all variables inside of soft constraints to true
  for (int cls_idx = 0; cls_idx  < yals->nclauses; cls_idx ++) {
    if (yals->hard_clause_ids [cls_idx]) continue;
    lits = yals_lits (yals, cls_idx);
    for (p = lits; (lit = *p); p++ ) {
      if (!hard_polarity) SETBIT (yals->vals, yals->nvarwords, ABS (lit));
      else CLRBIT (yals->vals, yals->nvarwords, ABS (lit));
    }
  }
  for (int cls_idx = 0; cls_idx  < yals->card_nclauses; cls_idx ++) {
    if (yals->hard_card_ids [cls_idx]) continue;
    lits = yals_card_lits (yals, cls_idx);
    for (p = lits; (lit = *p); p++ ) {
      if (!hard_polarity) SETBIT (yals->vals, yals->nvarwords, ABS (lit));
      else CLRBIT (yals->vals, yals->nvarwords, ABS (lit));
    }
  }

  // setting propagated hard units
  yals_set_units (yals);
  yals_update_sat_and_unsat (yals);

  yals_msg (yals, 1, "Phase 2 : satisfying all hard constraints");
  LOG ("Phase 2: fixing hard constraints");
  // fix all hard constraints
  while (COUNT (yals->unsat.stack)) { // while there are falsified hard clauses
    // pick an unsat clause
    int cidx, cpos = 0;
    if (yals->pick == 0) {
      cpos = yals_rand_mod (yals, COUNT (yals->unsat.stack));
    }
    cidx = PEEK (yals->unsat.stack, cpos);
    assert (yals->pos[cidx] == cpos);

    // satisfy by flipping best literal
    lit = yals_best_lit_on_init (yals, cidx, TYPECLAUSE);
    assert (lit/ABS(lit) == yals->hard_polarity);
    yals_flip_on_init (yals, lit);
  }

  while (COUNT (yals->card_unsat.stack)) { // while there are falsified hard cardinality constraints
    // pick an unsat cardinality constraint
    int cidx, cpos = 0;
    if (yals->pick == 0) {
      cpos = yals_rand_mod (yals, COUNT (yals->card_unsat.stack));
    }
    cidx = PEEK (yals->card_unsat.stack, cpos);
    assert (yals->card_pos[cidx] == cpos);

    lit = yals_best_lit_on_init (yals, cidx, TYPECARDINALITY);
    assert (lit/ABS(lit) == yals->hard_polarity);
    yals_flip_on_init (yals, lit);
  }

  // reset flip statistics (not really necessary if we are not restarting...)
  yals->stats.tmp = INT_MAX;
  yals->stats.maxs_tmp_weight = YALS_DOUBLE_MAX;
  yals_save_new_minimum_cost (yals);
  yals->stats.last = yals_nunsat (yals);
  yals->stats.maxs_last = yals->stats.maxs_best_cost;

  yals->stats.maxs_time.initialization += yals_time_phase (yals) - start;

  yals_maxs_check_global_satisfaction_invariant (yals);
}

/*
// unimplemented
// probably more useful for MaxSAT
void yals_init_assignment_deci (Yals *yals) {

  return ;
}
*/


/*
  MaxSAT outer loop restarts

  Same as inner loop restart except it permanently changes exploration limits
*/
static void yals_maxs_restart_outer (Yals * yals) {
  double start;
  size_t bytes = yals->nvarwords * sizeof (Word);

  start = yals_time_phase (yals);
  yals->stats.restart.outer.count++;

  yals_maxs_report (yals, "outer restart %lld", yals->stats.restart.outer.count);

  yals->stats.pick.best++;
  yals_msg (yals, 1, "Restart: picking previous best assignment");
  memcpy (yals->vals, yals->best, bytes);
  yals_update_sat_and_unsat (yals);

  yals->stats.last = yals->stats.best;
  yals->stats.maxs_last = yals->stats.maxs_best_cost;

  yals->stats.time.restart += yals_time_phase (yals) - start;


  // new configuration settings
  yals->opts.hard_stochastic_selection.val = MIN (((yals->opts.hard_stochastic_selection.val + 1) ), 10);
  yals->opts.maxs_hit_bound.val = MIN (((yals->opts.maxs_hit_bound.val + 5) ), 100);
}

/*
  MaxSAT inner loop restarts

  - return to previous best solution
  - reset initial DDFW weights
*/
static void yals_maxs_restart_inner (Yals * yals) {
  double start;
  size_t bytes = yals->nvarwords * sizeof (Word);
  start = yals_time_phase (yals);
  yals->stats.restart.inner.count++;
  yals_maxs_report (yals, "restart %lld", yals->stats.restart.inner.count);

  // keep current assignment
  if ((int) yals_rand_mod (yals, 100000) <=  yals->opts.maxs_keep_assignment.val) {
    yals_msg (yals, 1, "Restart: keeping current assignment");
    yals_update_sat_and_unsat (yals);
  } else { // pick previous best assignment
    yals->stats.pick.best++;
    yals_msg (yals, 1, "Restart: picking previous best assignment");
    memcpy (yals->vals, yals->best, bytes);
    yals_update_sat_and_unsat (yals); // reset DDFW weights
    yals->stats.last = yals->stats.best;
    yals->stats.maxs_last = yals->stats.maxs_best_cost;
  }

  yals->stats.time.restart += yals_time_phase (yals) - start;
}

/*
  Pure MaxSAT inner loop
*/
int yals_pure_maxs_inner_loop (Yals * yals) {
  LOG ("Pure MaxSAT inner loop with %d max tries with %d cutoff", yals->opts.maxtries.val,yals->opts.cutoff.val);
  int lit = 0, c = 0, hit = 0, orig_hit_bound, hit_bound;
  int phase1_flips = 1;
  int inner_flips, inner_bound, orig_inner_bound;
  int outer_flips, outer_bound;

  orig_inner_bound = inner_bound = yals->opts.maxs_inner_bound.val;
  hit_bound = orig_hit_bound = yals->opts.maxs_hit_bound.val;
  inner_flips = outer_flips = 0;
  outer_bound = yals->opts.maxs_outer_restart.val;

  for (int t=0; t<yals->opts.maxtries.val; t++)
  {
    if (!yals_get_cost (yals))
      return 1;

    // if (!yals->opts.ddfwonly.val) // currently not allowed...
          // this is where you could toss in a faster descent

    while ( c<yals->opts.cutoff.val || (yals->opts.cutoff.val <= 0)) // cutoff=0 is unlimited flips
    {
      yals_msg (yals, 2, "Phase 0 : check if new best assignment");
      if (!yals_nunsat(yals)) { // Check if new best assignment
        // yals_satisfy_trivial_soft (yals); // handled implicitly with heap (free flips always at the top...)
        yals_save_new_minimum_cost (yals);
        if (!yals_get_cost (yals)) // 0 cost solution, all soft constraints satisfied
          return 1;

        // reset limits
        phase1_flips = 1;
        inner_flips = 0;
        hit = 0;
        hit_bound = orig_hit_bound;
        inner_bound = orig_inner_bound;
      } else if (yals->opts.maxs_outer_restart.val && outer_flips > outer_bound) {
        // outer restart
        yals_maxs_restart_outer (yals);

        // reset limits
        orig_hit_bound = yals->opts.maxs_hit_bound.val;
        outer_flips = 0;
        phase1_flips = 1;
        inner_flips = 0;
        hit = 0;
        hit_bound = orig_hit_bound;
        inner_bound = orig_inner_bound;
      } else if (inner_flips > inner_bound) {
        // increase exploration
        phase1_flips += yals->opts.maxs_flip_step.val;

        // may transfer weight to soft constraints
        if (yals->opts.maxs_transfer_soft.val) {
          yals->weight_transfer_soft = 1;
          yals_transfer_weights (yals);
          yals_check_global_satisfaction_invariant (yals);
          yals->weight_transfer_soft = 0;
        }
        
        hit++;
        inner_flips = 0;
      } else { // slow weight transfer only when no better cost solution found
          if (yals->opts.maxs_transfer_slow.val)
              yals_transfer_weights (yals);
      }

      

      if (hit > hit_bound) {
        // inner restart
        yals_maxs_restart_inner (yals);

        hit = 0;

        // increase exploration limits
        hit_bound *= yals->opts.maxs_inner_mult.val / 10.0;
        inner_bound *= yals->opts.maxs_inner_mult.val / 10.0;
      }

      yals_msg (yals, 2, "Hard polarity %d",yals->hard_polarity);
      yals_msg (yals, 2, "Phase 1 : explore soft optimization");
      // Phase 1: explore by satisfying soft consrtaints
      for (int i = 0; i < phase1_flips; i++) {
        if (!yals_soft_unsat (yals)) break;
        double start = yals_time_phase (yals);
        lit = yals_pick_literal_from_heap (yals, 1);
        yals->stats.maxs_time.var_selection += yals_time_phase (yals) - start;
        yals->stats.maxs_time.soft_var_selection += yals_time_phase (yals) - start;
        inner_flips++;
        outer_flips++;
        c++;
        assert (lit);
        assert (lit/ABS(lit) == yals->hard_polarity);
        yals_flip_ddfw (yals, lit);
      }

      yals_msg (yals, 2, "Phase 2 : fix hard constraints");
      // Phase 2: fix hard constraints
      while (yals_nunsat (yals)) {
        double start = yals_time_phase (yals);
        lit = yals_pick_literal_from_heap (yals, 0);
        yals->stats.maxs_time.var_selection += yals_time_phase (yals) - start;
        yals->stats.maxs_time.hard_var_selection += yals_time_phase (yals) - start;
        if (!lit) break; // may occur since we don't push previous tries back on heap...
        assert (lit/ABS(lit) != yals->hard_polarity);
        if (yals_soft_cost_of_flip (yals, -lit) < yals->stats.maxs_best_cost) {
          yals_flip_ddfw (yals, lit);
          outer_flips++;
          c++;
          // inner_flips++; // lets only count soft flips
        }
        else {
          // push back on? (experimentally, seems to be better if we leave it off)
          break;
        }
      }

      yals_msg (yals, 2, "Phase 3 : weight transfer");
      // Phase 3: weight transfer
      if (!yals->opts.maxs_transfer_slow.val) // fast weight transfer
        yals_transfer_weights (yals);
      yals_check_global_satisfaction_invariant (yals);
      c++;
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