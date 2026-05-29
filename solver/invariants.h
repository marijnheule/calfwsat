/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and manager  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _invariant_h_INCLUDED
#define _invariant_h_INCLUDED

#include "yals.h"
#include <math.h>
#include "yils_card.h"
#include "inlineheap.h"


/*

  Invariants to check various properties of the solver during execution.

  Run with `-c ` after compiling with debugging.

  Invariant checking will significantly slow down the solver on larger
  instances.

  Invariant checks:

  (1) Check "best variable" has the best ddfw weight change
      - not applicable if using stochastic choice

  (2) Check ddfw weight changes for variables match ddfw weights of constraints.
      Check ddfw weight calculation is correct for cardinality constraints.
      Check total ddfw weight in system has not changed during execution.

  (3) Check falsified constraints are on unsat stacks.
      Check constraints have correct nsat (number satisfied literals) counts.

*/


/*------------------------------------------------------------------------*/


/*

  Check that the best picked ddfw var is actually the best to flip

  This invariant can fail if the set uvars is not complete

*/ 
static void yals_check_global_best_weight_invariant (Yals * yals) {
  #ifndef NDEBUG
  if (!yals->opts.checking.val) return;
  if (yals->opts.hard_stochastic_selection.val > 1 || yals->opts.maxs_soft_stochastic_selection.val > 1) return;

  int max_var = -1, var, true_lit, false_lit;
  double max_gain = INT_MIN*1.0, flip_gain;
  for (var=1; var < yals->nvars; var++) {
    
    true_lit = yals_val (yals, var) ? var : -var;
    false_lit = -true_lit;

    // should always be a positive ddfw weight 
    assert (yals->ddfw.sat1_weights [get_pos (true_lit)] >= -0.1);

    flip_gain =
        yals->ddfw.unsat_weights [get_pos (false_lit)]  
        - yals->ddfw.sat1_weights [get_pos (true_lit)];

    if (flip_gain > max_gain) {
      max_gain = flip_gain;
      max_var = true_lit;
    }

    if (flip_gain > 0 && var != yals->ddfw.best_var) {
      LOG ("determine uwvar %d with gain %lf", var, flip_gain);
      assert (yals_heap_contains (&yals->ddfw.uvars_heap, var));
      assert (yals->ddfw.uvars_heap.score [var] == flip_gain);
    }

  }

  if (!yals->ddfw.best_var) {
    assert (max_gain <= 0);
    return;
  }
  LOG ("Expected max var %d best gain %lf", max_var, max_gain);
  LOG ("Found max var %d best gain %lf", yals->ddfw.best_var, yals->ddfw.best_weight);
  if (max_gain > 0.1) {
    if (!(fabs (yals->ddfw.best_weight - max_gain) < 0.1)) {
      printf ("Expected max var %d pos %d best gain %lf\n", max_var, yals->ddfw.uvar_pos[abs(max_var)],max_gain);
      printf ("Unsat %lf sat %lf\n",yals->ddfw.unsat_weights [get_pos (-max_var)],yals->ddfw.sat1_weights [get_pos (max_var)] );
      printf ("Found max var %d best gain %lf\n", yals->ddfw.best_var, yals->ddfw.best_weight);
    }
    assert (fabs (yals->ddfw.best_weight - max_gain) < 0.1);
  }
  #endif
}

/*

  Check the ddfw accumulated weights for each literal

  Loops over all constraints, checking that the total constraint weight is correct. 
  The total should not change over the course of the algorithm because constraints 
  transfer weight to each other in a way that conserves the total amount of weight 
  in the system. Also checks that the accumulated unsat and sat weights for each 
  literal is correct. These are the weights that determine the gain when flipping 
  the literal. 

*/
static void yals_check_global_weight_invariant (Yals * yals) {
  #ifndef NDEBUG
  if (!yals->opts.checking.val) return;
  if (yals->using_maxs_weights) {
    yals_maxs_check_global_weight_invariant (yals);
    return;
  }

  int cidx, lit, temp_iter, bound;
  const int * p;

  double expected_unsat_weights[2* yals->nvars];
  double expected_sat1_weights[2* yals->nvars];
  for (temp_iter = -yals->nvars + 1; temp_iter < yals->nvars; temp_iter++) {
    if (temp_iter == 0) continue;
    expected_unsat_weights[get_pos (temp_iter)] = 0;
    expected_sat1_weights[get_pos (temp_iter)] = 0;
  }

  double actual_total_weight, expected_total_weight;
  actual_total_weight = expected_total_weight = 0;

  LOG("Clause weights"); // printing out each constraints weights
  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    if (yals_satcnt (yals, cidx) > 0) {
      LOGCIDX (cidx, "SAT Weight %lf",yals->ddfw.ddfw_clause_weights[cidx]);
    } else {
      LOGCIDX (cidx, "UNSAT Weight %lf",yals->ddfw.ddfw_clause_weights[cidx]);
    }
    actual_total_weight += yals->ddfw.ddfw_clause_weights[cidx];
    expected_total_weight += yals->opts.init_clause_weight.val; // each clause started with this

    // look at actual unsat and sat1 weights
    unsigned sat;
    for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++) {
      if (yals_val (yals, lit)) sat++;
    }
    if (sat == 1) {
      for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (yals_val (yals, lit)) expected_sat1_weights[get_pos (lit)] += yals->ddfw.ddfw_clause_weights[cidx];
      }
    } else if (sat == 0) {
      for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        expected_unsat_weights[get_pos (lit)] += yals->ddfw.ddfw_clause_weights[cidx];
      }
    }
  }
  LOG("Cardinality weights"); // printing out each constraints weights
  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    if (yals_card_satcnt (yals, cidx) >= yals_card_bound (yals, cidx)) {
      LOGCARDCIDX (cidx, "SAT Weight %lf",yals->ddfw.ddfw_card_weights[cidx]); 
    } else {
      LOGCARDCIDX (cidx, "UNSAT Weight %lf",yals->ddfw.ddfw_card_weights[cidx]); 
    }
    actual_total_weight += yals->ddfw.ddfw_card_weights[cidx];
    expected_total_weight += yals->opts.init_card_weight.val; // each cardinality constraint started with this

    // look at actual unsat and sat1 weights
    unsigned sat;
    bound = yals_card_bound (yals, cidx);
    for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++) {
      if (yals_val (yals, lit)) sat++;
    }
    if (sat == bound) {
      assert (yals_card_get_calculated_weight_change_neg (yals, cidx) >= 0);
      for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (yals_val (yals, lit)) expected_sat1_weights[get_pos (lit)] += yals_card_get_calculated_weight_change_neg (yals, cidx);
      }
    } else if (sat < bound) {
      assert (yals_card_get_calculated_weight_change_neg (yals, cidx) >= 0);
      assert (yals_card_get_calculated_weight (yals, cidx) >= 0);
      for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (yals_val (yals, lit)) expected_sat1_weights[get_pos (lit)] += yals_card_get_calculated_weight_change_neg (yals, cidx);
        else expected_unsat_weights[get_pos (lit)] += yals_card_get_calculated_weight (yals, cidx);
      }
    }

  }

  LOG("Actual %lf Expected %lf",actual_total_weight,expected_total_weight);
  assert (actual_total_weight == expected_total_weight); // total weight should never change

  // check that unsat and sat1 weights are correct
  // i.e., the literal weight changes reflect the actual weight from each constraint

  for (temp_iter = -yals->nvars + 1; temp_iter < yals->nvars; temp_iter++) {
    if (temp_iter == 0) continue;

    LOG ("Lit %d, unsat expected %lf actual %lf, sat expected %lf actual %lf",\
    temp_iter, expected_unsat_weights[get_pos (temp_iter)],yals->ddfw.unsat_weights[get_pos (temp_iter)],expected_sat1_weights[get_pos (temp_iter)],yals->ddfw.sat1_weights[get_pos (temp_iter)] );

    // if assertion is about to fail, print out the information necessary for debugging
    if (!(fabs (expected_unsat_weights[get_pos (temp_iter)] - yals->ddfw.unsat_weights[get_pos (temp_iter)]) < .01) ||\
    !(fabs (expected_sat1_weights[get_pos (temp_iter)] - yals->ddfw.sat1_weights[get_pos (temp_iter)]) < 0.1) ) {

      yals_msg (yals, 1, "Lit %d, unsat expected %lf actual %lf, sat expected %lf actual %lf",\
    temp_iter, expected_unsat_weights[get_pos (temp_iter)],yals->ddfw.unsat_weights[get_pos (temp_iter)],expected_sat1_weights[get_pos (temp_iter)],yals->ddfw.sat1_weights[get_pos (temp_iter)] );
    }

    assert (fabs (expected_unsat_weights[get_pos (temp_iter)] - yals->ddfw.unsat_weights[get_pos (temp_iter)]) < .01);

    assert (fabs (expected_sat1_weights[get_pos (temp_iter)] - yals->ddfw.sat1_weights[get_pos (temp_iter)]) < 0.1);
  }

  #endif
}

/*

  Check the ddfw accumulated weights for each literal

  Loops over all constraints, checking that the total constraint weight is correct. 
  The total should not change over the course of the algorithm because constraints 
  transfer weight to each other in a way that conserves the total amount of weight 
  in the system. Also checks that the accumulated unsat and sat weights for each 
  literal is correct. These are the weights that determine the gain when flipping 
  the literal. 

*/
void yals_maxs_check_global_weight_invariant (Yals * yals) {
  #ifndef NDEBUG
  if (!yals->opts.checking.val) return;

  int cidx, lit, temp_iter, bound, soft;
  const int * p;

  LOG ("Starting global weight invariant");

  double expected_unsat_weights[2* yals->nvars];
  double expected_sat1_weights[2* yals->nvars];
  double *expected_unsat_weights_soft;
  double *expected_sat1_weights_soft;
  NEWN (expected_sat1_weights_soft, 2* yals->nvars);
  NEWN (expected_unsat_weights_soft, 2* yals->nvars);
  for (temp_iter = -yals->nvars + 1; temp_iter < yals->nvars; temp_iter++) {
    if (temp_iter == 0) continue;
    expected_unsat_weights[get_pos (temp_iter)] = 0;
    expected_sat1_weights[get_pos (temp_iter)] = 0;
    expected_unsat_weights_soft[get_pos (temp_iter)] = 0;
    expected_sat1_weights_soft[get_pos (temp_iter)] = 0;
  }

  double actual_total_weight, expected_total_weight;
  actual_total_weight = expected_total_weight = 0;

  LOG("Clause weights"); // printing out each constraint's weights
  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    soft = 0;
    if (!yals->hard_clause_ids[cidx]) soft = 1;
    if (yals_satcnt (yals, cidx) > 0) {
      LOGCIDX (cidx, "SOFT?%d SAT Weight %lf and multiplier %lf",soft,yals->ddfw.ddfw_clause_weights[cidx],PEEK (yals->maxs_clause_weights,cidx));
    } else {
      LOGCIDX (cidx, "SOFT?%d UNSAT Weight %lf and multiplier %lf",soft,yals->ddfw.ddfw_clause_weights[cidx],PEEK (yals->maxs_clause_weights,cidx));
    }


    double maxs_weight = 1.0;

    if (!yals->opts.maxs_init_weight_relative.val && soft)
      maxs_weight = PEEK (yals->maxs_clause_weights, cidx);

    if (yals->opts.maxs_init_weight_relative.val && soft) {
      expected_total_weight += PEEK (yals->maxs_clause_weights, cidx);
    } else expected_total_weight += yals->opts.init_clause_weight.val; // each clause started with this
    
    actual_total_weight += yals->ddfw.ddfw_clause_weights[cidx];
    
    // look at actual unsat and sat1 weights
    unsigned sat;
    for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++) {
      if (yals_val (yals, lit)) sat++;
    }
    if (sat == 1) {
      for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (yals_val (yals, lit)) {
          if (soft)
            expected_sat1_weights_soft[get_pos (lit)] += yals->ddfw.ddfw_clause_weights[cidx] * maxs_weight;
          else 
            expected_sat1_weights[get_pos (lit)] += yals->ddfw.ddfw_clause_weights[cidx];
        }
      }
    } else if (sat == 0) {
      for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (soft)
          expected_unsat_weights_soft[get_pos (lit)] += yals->ddfw.ddfw_clause_weights[cidx] * maxs_weight;
        else
          expected_unsat_weights[get_pos (lit)] += yals->ddfw.ddfw_clause_weights[cidx];
      }
    }
  }
  LOG("Cardinality weights"); // printing out each constraints weights
  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    soft = 0;
    if (!yals->hard_card_ids[cidx]) soft = 1;
    if (yals_card_satcnt (yals, cidx) >= yals_card_bound (yals, cidx)) {
      LOGCARDCIDX (cidx, "SOFT?%d SAT Weight %lf and multiplier %lf",soft,yals->ddfw.ddfw_card_weights[cidx], PEEK (yals->maxs_card_weights,cidx)); 
    } else {
      LOGCARDCIDX (cidx, "SOFT?%d UNSAT Weight %lf and multiplier %lf",soft,yals->ddfw.ddfw_card_weights[cidx], PEEK (yals->maxs_card_weights,cidx)); 
    }

    double maxs_weight = 1.0;

    if (!yals->opts.maxs_init_weight_relative.val && soft)
      maxs_weight = PEEK (yals->maxs_card_weights, cidx);

    if (yals->opts.maxs_init_weight_relative.val && soft) {
      expected_total_weight += PEEK (yals->maxs_card_weights, cidx);
    } else expected_total_weight += yals->opts.init_card_weight.val; // each clause started with this

    actual_total_weight += yals->ddfw.ddfw_card_weights[cidx];

    // look at actual unsat and sat1 weights
    unsigned sat;
    bound = yals_card_bound (yals, cidx);
    for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++) {
      if (yals_val (yals, lit)) sat++;
    }
    if (sat == bound) {
      assert (yals_card_get_calculated_weight_change_neg (yals, cidx) >= 0);
      for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (yals_val (yals, lit)) {
          if (soft)
            expected_sat1_weights_soft[get_pos (lit)] += yals_card_get_calculated_weight_change_neg (yals, cidx);
          else
            expected_sat1_weights[get_pos (lit)] += yals_card_get_calculated_weight_change_neg (yals, cidx);
        }
      }
    } else if (sat < bound) {
      assert (yals_card_get_calculated_weight_change_neg (yals, cidx) >= 0);
      assert (yals_card_get_calculated_weight (yals, cidx) >= 0);
      for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++) {
        if (yals_val (yals, lit)) {
           if (soft)
            expected_sat1_weights_soft[get_pos (lit)] += yals_card_get_calculated_weight_change_neg (yals, cidx);
          else
            expected_sat1_weights[get_pos (lit)] += yals_card_get_calculated_weight_change_neg (yals, cidx);
        }
        else {
          if (soft)
            expected_unsat_weights_soft[get_pos (lit)] += yals_card_get_calculated_weight (yals, cidx);
          else
            expected_unsat_weights[get_pos (lit)] += yals_card_get_calculated_weight (yals, cidx);
        }
      }
    }

  }

  LOG("Actual %lf Expected %lf",actual_total_weight,expected_total_weight);
  assert (actual_total_weight == expected_total_weight); // total weight should never change

  // check that unsat and sat1 weights are correct
  // i.e., the literal weight changes reflect the actual weight from each constraint

  for (temp_iter = -yals->nvars + 1; temp_iter < yals->nvars; temp_iter++) {
    if (temp_iter == 0) continue;

    LOG ("Hard lit %d, unsat expected %lf actual %lf, sat expected %lf actual %lf",\
    temp_iter, expected_unsat_weights[get_pos (temp_iter)],yals->ddfw.unsat_weights[get_pos (temp_iter)],expected_sat1_weights[get_pos (temp_iter)],yals->ddfw.sat1_weights[get_pos (temp_iter)] );

    // if assertion is about to fail, print out the information necessary for debugging
    if (!(fabs (expected_unsat_weights[get_pos (temp_iter)] - yals->ddfw.unsat_weights[get_pos (temp_iter)]) < .01) ||\
    !(fabs (expected_sat1_weights[get_pos (temp_iter)] - yals->ddfw.sat1_weights[get_pos (temp_iter)]) < 0.1) ) {

      yals_msg (yals, 1, "Lit %d, unsat expected %lf actual %lf, sat expected %lf actual %lf",\
    temp_iter, expected_unsat_weights[get_pos (temp_iter)],yals->ddfw.unsat_weights[get_pos (temp_iter)],expected_sat1_weights[get_pos (temp_iter)],yals->ddfw.sat1_weights[get_pos (temp_iter)] );
    }

    assert (fabs (expected_unsat_weights[get_pos (temp_iter)] - yals->ddfw.unsat_weights[get_pos (temp_iter)]) < .01);

    assert (fabs (expected_sat1_weights[get_pos (temp_iter)] - yals->ddfw.sat1_weights[get_pos (temp_iter)]) < 0.1);

    LOG ("Soft lit %d, unsat expected %lf actual %lf, sat expected %lf actual %lf",\
    temp_iter, expected_unsat_weights_soft[get_pos (temp_iter)],yals->ddfw.unsat_weights_soft[get_pos (temp_iter)],expected_sat1_weights_soft[get_pos (temp_iter)],yals->ddfw.sat1_weights_soft[get_pos (temp_iter)] );

    // if assertion is about to fail, print out the information necessary for debugging
    if (!(fabs (expected_unsat_weights_soft[get_pos (temp_iter)] - yals->ddfw.unsat_weights_soft[get_pos (temp_iter)]) < .01) ||\
    !(fabs (expected_sat1_weights_soft[get_pos (temp_iter)] - yals->ddfw.sat1_weights_soft[get_pos (temp_iter)]) < 0.1) ) {

      yals_msg (yals, 1, "Lit %d, unsat expected %lf actual %lf, sat expected %lf actual %lf",\
    temp_iter, expected_unsat_weights_soft[get_pos (temp_iter)],yals->ddfw.unsat_weights_soft[get_pos (temp_iter)],expected_sat1_weights_soft[get_pos (temp_iter)],yals->ddfw.sat1_weights_soft[get_pos (temp_iter)] );
    }

    assert (fabs (expected_unsat_weights_soft[get_pos (temp_iter)] - yals->ddfw.unsat_weights_soft[get_pos (temp_iter)]) < .01);

    assert (fabs (expected_sat1_weights_soft[get_pos (temp_iter)] - yals->ddfw.sat1_weights_soft[get_pos (temp_iter)]) < 0.1);
  }

  LOG ("Finished global weight invariant");

  DELN (expected_sat1_weights_soft, 2* yals->nvars);
  DELN (expected_unsat_weights_soft, 2* yals->nvars);

  #endif
}

/*
  Check satisfiaction of each constraint.

  Check that each unsatisfied constraint is in the correct unsat queue. 
  Check that for each constraint, the number of satisfied literals (stored 
  in an array) matches the actual number of satisfied literals)
*/
static void yals_check_global_satisfaction_invariant (Yals * yals) {
if (yals->using_maxs_weights) {yals_maxs_check_global_satisfaction_invariant (yals); return;}
#ifndef NDEBUG
  LOG ("Check Global Invariant");
  int cidx, lit, nunsat = 0;
  const int * p;
  assert (BITS_PER_WORD == (1 << LD_BITS_PER_WORD));
  if (!yals->opts.checking.val) return;
  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    unsigned sat;
    for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++)
      if (yals_val (yals, lit)) sat++;
    assert (yals_satcnt (yals, cidx) == sat);
    if (!sat) nunsat++;
    if (yals->unsat.usequeue) {
      Lnk * l = yals->lnk[cidx];
      assert (l);
      assert (l->cidx == cidx);
    } else {
      int pos = yals->pos[cidx];
      if (sat) assert (pos < 0);
      else {
// assert_valid_pos (pos);
assert (PEEK (yals->unsat.stack, pos) == cidx);
      }
    }
  }
  // LOG ("nunsat %d, clauses unsat %d", nunsat, yals_clauses_nunsat (yals));
  assert (nunsat == yals_clauses_nunsat (yals));
#endif
  (void) yals;

  // cardinality constraint invariants
  #ifndef NDEBUG
  int bound;
  nunsat = 0;
  assert (BITS_PER_WORD == (1 << LD_BITS_PER_WORD));
  if (!yals->opts.checking.val) return;
  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    unsigned sat;
    bound = yals_card_bound (yals, cidx);
    for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++)
      if (yals_val (yals, lit)) sat++;
    LOGCARDCIDX (cidx, "nsat %d satcnt %d", sat, yals_card_satcnt (yals, cidx) );
    assert (yals_card_satcnt (yals, cidx) == sat);
    if (sat < bound) nunsat++;
    if (yals->card_unsat.usequeue) {
      Lnk * l = yals->lnk[cidx];
      assert (l);
      assert (l->cidx == cidx);
    } else {
      int pos = yals->card_pos[cidx];
      if (sat >= bound) assert (pos < 0);
      else {
assert_valid_card_pos (pos);
assert (PEEK (yals->card_unsat.stack, pos) == cidx);
      }
    }
  }
  assert (nunsat == yals_card_nunsat (yals)); // counting number falsified constraints correctly
#endif
  (void) yals;

#ifndef NDEBUG
  yals_check_global_weight_invariant (yals); // also check weights
#endif


}



/*
  Check satisfiaction of each constraint.

  Check that each unsatisfied constraint is in the correct unsat queue. 
  Check that for each constraint, the number of satisfied literals (stored 
  in an array) matches the actual number of satisfied literals)
*/
void yals_maxs_check_global_satisfaction_invariant (Yals * yals) {
  assert (yals->using_maxs_weights);
#ifndef NDEBUG
  LOG ("Check Global Satisfaction Invariant for MaxSAT");
  int cidx, lit, nunsat = 0, nunsat_soft = 0;
  const int * p;
  assert (BITS_PER_WORD == (1 << LD_BITS_PER_WORD));
  if (!yals->opts.checking.val) return;
  for (cidx = 0; cidx < yals->nclauses; cidx++) {
    unsigned sat;
    for (p = yals_lits (yals, cidx), sat = 0; (lit = *p); p++)
      if (yals_val (yals, lit)) sat++;
    assert (yals_satcnt (yals, cidx) == sat);
    if (!yals->hard_clause_ids[cidx]) {
      if (!sat) nunsat_soft++;
      int pos = yals->pos_soft[cidx];
      if (sat) assert (pos < 0);
      else {
        // // assert_valid_pos (pos);
        assert (PEEK (yals->unsat_soft.stack, pos) == cidx);
      }
    } else {
      if (!sat) nunsat++;
      int pos = yals->pos[cidx];
      if (sat) assert (pos < 0);
      else {
        // assert_valid_pos (pos);
        assert (PEEK (yals->unsat.stack, pos) == cidx);
      }
    }
  }
  // LOG ("nunsat %d, clauses unsat %d", nunsat, yals_clauses_nunsat (yals));
  assert (nunsat == yals_clauses_nunsat (yals));
  assert (nunsat_soft == COUNT (yals->unsat_soft.stack));
#endif
  (void) yals;

  // cardinality constraint invariants
  #ifndef NDEBUG
  int bound;
  nunsat = nunsat_soft = 0;
  assert (BITS_PER_WORD == (1 << LD_BITS_PER_WORD));
  if (!yals->opts.checking.val) return;
  for (cidx = 0; cidx < yals->card_nclauses; cidx++) {
    unsigned sat;
    bound = yals_card_bound (yals, cidx);
    for (p = yals_card_lits (yals, cidx), sat = 0; (lit = *p); p++)
      if (yals_val (yals, lit)) sat++;
    LOGCARDCIDX (cidx, "nsat %d satcnt %d", sat, yals_card_satcnt (yals, cidx) );
    assert (yals_card_satcnt (yals, cidx) == sat);
    if (!yals->hard_card_ids[cidx]) {
      if (sat < bound) nunsat_soft++;
      int pos = yals->card_pos_soft[cidx];
      if (sat >= bound) assert (pos < 0);
      else {
        // assert_valid_card_pos (pos);
        assert (PEEK (yals->card_unsat_soft.stack, pos) == cidx);
      }
    } else {
      if (sat < bound) nunsat++;
      int pos = yals->card_pos[cidx];
      if (sat >= bound) assert (pos < 0);
      else {
        assert_valid_card_pos (pos);
        assert (PEEK (yals->card_unsat.stack, pos) == cidx);
      }
    }
  }
  LOG ("Finished Cardinality");
  assert (nunsat == yals_card_nunsat (yals)); // counting number falsified constraints correctly
  assert (nunsat_soft == COUNT (yals->card_unsat_soft.stack));
  LOG ("Finished Global Satisfiability Invariant");
#endif
  (void) yals;

#ifndef NDEBUG
  yals_maxs_check_global_weight_invariant (yals);
#endif
}

#endif