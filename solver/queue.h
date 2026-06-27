/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _queue_h_INCLUDED
#define _queue_h_INCLUDED

#include "yals.h"
#include "yils_card.h"
#include "invariants.h"


/*

  Falsified constraints are stored on a stack.

  A linked-list queue implementation used to live here too, but it was
  hardcoded off (pick==0 => unsat is always a stack), so the queue functions
  and all of its supporting struct fields (usequeue, Queue/Chunk/Lnk, the
  defrag option and stats) have been removed.

  We have the following stacks:
    yals->unsat for falsified clauses,
    yals_card_unsat for falsified cardinality constraints,

  The stack is necessary for the WT base algorithm. It allows us to
  loop over falsified constraints during the weight transfer.

  The stack is also used to implement a probSAT-like algorithm
  for fast descent at the beginning of the execution.

*/

/*------------------------------------------------------------------------*/

static inline void yals_dequeue_stack (Yals * yals, int cidx, int constraint_type) {
  int * pos = 0;
  UNSAT_STACK *unsat = 0;
  if (constraint_type == TYPECLAUSE) {
    unsat = &(yals->unsat);
    pos = yals->pos;
  } else if (constraint_type == TYPECARDINALITY) {
    unsat = &(yals->card_unsat);
    pos = yals->card_pos;
  } else {yals_abort (yals, "incorrect constraint type");}

  int cpos = pos[cidx], didx;
  // // assert_valid_pos (cpos);
  assert (PEEK (unsat->stack, cpos) == cidx);
  didx = POP (unsat->stack);
  if (didx != cidx) {
    assert (pos[didx] == COUNT (unsat->stack));
    POKE (unsat->stack, cpos, didx);
    pos[didx] = cpos;
  }
  pos[cidx] = -1;
}

static inline void yals_dequeue (Yals * yals, int cidx, int constraint_type) {
  LOG ("dequeue %d", cidx);

  if (constraint_type == TYPECLAUSE) {
    assert_valid_cidx (cidx);
    yals_dequeue_stack (yals, cidx, constraint_type);
    yals_delete_vars_from_uvars (yals, cidx, TYPECLAUSE);
  } else if (constraint_type == TYPECARDINALITY) {
    assert_valid_card_cidx (cidx);
    yals_dequeue_stack (yals, cidx, constraint_type);
    yals_delete_vars_from_uvars (yals, cidx, TYPECARDINALITY);
  } else yals_abort (yals, "incorrect constraint type");
}

static inline void yals_enqueue_stack (Yals * yals, int cidx, int constraint_type) {
  int size;
  int * pos = 0;
  UNSAT_STACK *unsat = 0;
  if (constraint_type == TYPECLAUSE) {
    unsat = &(yals->unsat);
    pos = yals->pos;
    if (yals->stats.maxstacksize < (size = SIZE (unsat->stack) + 1))
      yals->stats.maxstacksize = size;
  } else if (constraint_type == TYPECARDINALITY) {
    unsat = &(yals->card_unsat);
    pos = yals->card_pos;
    if (yals->stats.card_maxstacksize < (size = SIZE (unsat->stack) + 1))
      yals->stats.card_maxstacksize = size;
  } else {yals_abort (yals, "incorrect constraint type");}

  assert (pos[cidx] < 0);
  pos[cidx] = COUNT (unsat->stack);
  PUSH (unsat->stack, cidx);
}

static inline void yals_enqueue (Yals * yals, int cidx, int constraint_type) {
  LOG ("enqueue %d", cidx);

  if (constraint_type == TYPECLAUSE) {
    assert_valid_cidx (cidx);
    yals_enqueue_stack (yals, cidx, constraint_type);
    yals_add_vars_to_uvars (yals, cidx, TYPECLAUSE);
  } else if (constraint_type == TYPECARDINALITY) {
    assert_valid_card_cidx (cidx);
    yals_enqueue_stack (yals, cidx, constraint_type);
    yals_add_vars_to_uvars (yals, cidx, TYPECARDINALITY);
  } else yals_abort (yals, "incorrect constraint type");
}

static inline void yals_reset_unsat_stack (Yals * yals) {
  while (!EMPTY (yals->unsat.stack)) {
    int cidx = POP (yals->unsat.stack);
    assert_valid_cidx (cidx);
    assert (yals->pos[cidx] == COUNT (yals->unsat.stack));
    yals->pos[cidx] = -1;
  }
  RELEASE (yals->unsat.stack);
  yals->unsat.hard_cnt = 0;

  // cardinality stack
  while (!EMPTY (yals->card_unsat.stack)) {
    int cidx = POP (yals->card_unsat.stack);
    assert_valid_card_cidx (cidx);
    assert (yals->card_pos[cidx] == COUNT (yals->card_unsat.stack));
    yals->card_pos[cidx] = -1;
  }
  RELEASE (yals->card_unsat.stack);
  yals->card_unsat.hard_cnt = 0;
}


#endif
