/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef YILS_CARD_H_INCLUDED
#define YILS_CARD_H_INCLUDED

#ifndef YALSINTERNAL
#error "this file is internal to 'libyals'"
#endif

/*------------------------------------------------------------------------*/

#include "yals.h"

/*------------------------------------------------------------------------*/

#include <stdlib.h>

/*------------------------------------------------------------------------*/

/*

  Header file containing additional APIs for cardinality constraints
  and linear weight-transfers.

*/


/*------------------------------------------------------------------------*/

#ifndef NDEBUG
void yals_logging (Yals *, int logging);
void yals_checking (Yals *, int checking);
#endif

/*------------------------------------------------------------------------*/

const char * yals_default_prefix (void);
const char * yals_version ();
void yals_banner (const char * prefix);

/*------------------------------------------------------------------------*/

double yals_process_time ();				// process time

double yals_sec (Yals *);				// time in 'yals_sat'
size_t yals_max_allocated (Yals *);		// max allocated bytes

/*------------------------------------------------------------------------*/

void * yals_malloc (Yals *, size_t);
void yals_free (Yals *, void*, size_t);
void * yals_realloc (Yals *, void*, size_t, size_t);

/*------------------------------------------------------------------------*/

void yals_srand (Yals *, unsigned long long);

/* weight-transfer non-static methods */
int get_pos (int lit);
void yals_update_lit_weights_on_make (Yals * yals, int cidx, int lit);
void yals_update_lit_weights_at_start (Yals * yals, int cidx, int satcnt, int crit);
void yals_update_lit_weights_at_restart (Yals *yals);
void yals_compute_neighborhood_for_clause (Yals *yals, int cidx);
void yals_init_build (Yals *yals);
void yals_update_lit_weights_on_break (Yals * yals, int cidx, int lit);
void yals_add_vars_to_uvars (Yals* yals, int cidx, int constraint_type);
int yals_var_in_unsat (Yals *yals, int v);
void yals_delete_vars_from_uvars (Yals* yals, int cidx, int constraint_type);
void yals_update_var_unsat_count (Yals *yals, int cidx);
void yals_print_stats (Yals * yals);
void yals_update_uvars (Yals *yals, int cidx);
void set_options (Yals * yals);
void yals_outer_loop_maxtries (Yals * yals);
void yals_set_wid (Yals * yals, int widx);
int yals_inner_loop_max_tries (Yals * yals);
void yals_flip (Yals * yals, int lit);
void yals_transfer_weights (Yals *yals);

int * yals_card_lits (Yals * yals, int cidx);
int yals_card_bound (Yals * yals, int cidx) ;
int yals_card_length (Yals * yals, int cidx);

unsigned yals_card_satcnt (Yals * yals, int cidx);


void yals_card_sort_sat (Yals *yals, int cidx);
void yals_card_new_sat (Yals *yals, int cidx, int lit) ;
void yals_card_new_unsat (Yals *yals, int cidx, int lit) ;

void yals_card_sat_iters (Yals *yals, int cidx, int **begin, int **end) ;
void yals_card_unsat_iters (Yals *yals, int cidx, int **begin, int **end);
void yals_card_sat_weight_update (Yals *yals, int cidx, double w_diff, int avoid_lit);
void yals_card_unsat_weight_update (Yals *yals, int cidx, double w_diff, int avoid_lit) ;
double yals_card_calculate_weight (Yals * yals, int bound, int nsat, double c_weight, int cidx);
double yals_card_get_calculated_weight (Yals * yals, int cidx);
double yals_card_get_calculated_weight_change_pos (Yals * yals, int cidx);
double yals_card_get_calculated_weight_change_neg (Yals * yals, int cidx) ;

int yals_clauses_nunsat (Yals * yals);
int yals_card_nunsat (Yals * yals);
int yals_nunsat (Yals * yals);


void yals_preprocess (Yals * yals) ;

double default_card_wt (Yals * yals, int source, int sink);
void yals_transfer_weights_for_card (Yals *yals, int sink);


void yals_card_update_lit_weights_on_make (Yals * yals, int cidx, int lit);

void yals_card_update_lit_weights_at_start (Yals * yals, int cidx, int satcnt, int bound);

void yals_card_add_vars_to_uvars (Yals* yals, int cidx);
void yals_card_delete_vars_from_uvars (Yals* yals, int cidx, int constraint_type);
void yals_card_update_uvars (Yals *yals, int cidx);

void yals_new_cardinality_constraint (Yals * yals);
void yals_card_add (Yals * yals, int lit, int is_bound) ;


int * yals_card_occs (Yals * yals, int lit);

int yals_clauses_nunsat (Yals * yals);

int yals_card_nunsat (Yals * yals);


void yals_remove_a_var_from_uvars (Yals * yals , int v);
void yals_add_a_var_to_uvars (Yals * yals , int v);

#endif
