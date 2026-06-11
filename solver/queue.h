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

  The queue/stack is used to store falsified constraints.

  There is currently only support for a stack implementation, 
  the queue is disabled by hardcode in yals.c. The API is left
  around for the queue in case it becomes useufl in furture 
  work.

  We have the following stacks:
    yals->unsat for hard clauses (all constraints if not MaxSAT),
    yals_card_unsat for hard cardinality constraints (all constraints if not MaxSAT),
    yals->unsat_soft for soft clauses,
    yals_card_unsat_soft for soft cardinality constraints,

  The stack is necessary for the DDFW base algorithm. It allows us to 
  loop over falsified constraints during the weight transfer.

  The stack is also used to implement a probSAT-like algorithm
  for fast descent at the beginning of the execution. 

  It is used when initialization a solution for Pure MaxSAT, and may
  be useful for a general MaxSAT algorithm that takes steps similar
  to probSAT.

*/

/*------------------------------------------------------------------------*/

static void yals_enqueue_lnk (Yals * yals, Lnk * l) {
  Lnk * last = yals->unsat.queue.last;
  if (last) last->next = l;
  else yals->unsat.queue.first = l;
  yals->unsat.queue.last = l;
  l->prev = last;
  l->next = 0;
}

static void yals_dequeue_lnk (Yals * yals, Lnk * l) {
  Lnk * prev = l->prev, * next = l->next;
  if (prev) {
    assert (yals->unsat.queue.first);
    assert (yals->unsat.queue.last);
    assert (prev->next == l);
    prev->next = next;
  } else {
    assert (yals->unsat.queue.first == l);
    yals->unsat.queue.first = next;
  }
  if (next) {
    assert (yals->unsat.queue.first);
    assert (yals->unsat.queue.last);
    assert (next->prev == l);
    next->prev = prev;
  } else {
    assert (yals->unsat.queue.last == l);
    yals->unsat.queue.last = prev;
  }
}

/*------------------------------------------------------------------------*/

// START QUEUE

static void yals_flush_queue (Yals * yals) {
  int count = 0;
  Lnk * p;
  assert (yals->unsat.usequeue);
  for (p = yals->unsat.queue.first; p; p = p->next) {
    int cidx = p->cidx;
    assert_valid_cidx (cidx);
    assert (yals->lnk[cidx] == p);
    yals->lnk[cidx] = 0;
    count++;
  }
  yals->unsat.queue.first = yals->unsat.queue.last = 0;
  LOG ("flushed %d queue elements", count);
  assert (count == yals->unsat.queue.count);
  yals->unsat.queue.count = 0;
}

static void yals_release_lnks (Yals * yals) {
  int chunks = 0, lnks = 0;
  Chunk * q, * n;
  assert (yals->unsat.usequeue);
  for (q = yals->unsat.queue.chunks; q; q = n) {
    n = q->next;
    chunks++, lnks += q->size - 1;
    DELN (&q->lnks, q->size);
  }
  LOG ("released %d links in %d chunks", lnks, chunks);
  assert (yals->unsat.queue.nchunks == chunks);
  assert (yals->unsat.queue.nlnks == lnks);
  yals->unsat.queue.chunks = 0;
  yals->unsat.queue.free = 0;
  yals->unsat.queue.nfree = 0;
  yals->unsat.queue.chunksize = 0;
  yals->unsat.queue.nchunks = 0;
  yals->unsat.queue.nlnks = 0;
}

static void yals_reset_unsat_queue (Yals * yals) {
  assert (yals->unsat.usequeue);
  yals_flush_queue (yals);
  yals_release_lnks (yals);
}

static void yals_defrag_queue (Yals * yals) {
  const int count = yals->unsat.queue.count;
  const int size = MAX(2*(count + 1), yals->opts.minchunksize.val);
  Lnk * p, * first, * free, * prev = 0;
  double start = yals_time (yals);
  const Lnk * q;
  Chunk * c;
  assert (count);
  yals->stats.defrag.count++;
  yals->stats.defrag.moved += count;
  LOG ("defragmentation chunk of size %d moving %d", size, count);
  NEWN (p, size);
  c = (Chunk*) p;
  c->size = size;
  first = c->lnks + 1;
  for (q = yals->unsat.queue.first, p = first; q; q = q->next, p++) {
    *p = *q;
    p->prev = prev;
    if (prev) prev->next = p;
    prev = p;
  }
  assert (prev);
  prev->next = 0;
  free = p;
  yals_reset_unsat_queue (yals);
  assert (prev);
  yals->unsat.queue.first = first;
  yals->unsat.queue.last = prev;
  yals->unsat.queue.count = count;
  for (p = yals->unsat.queue.first; p; p = p->next) {
    int cidx = p->cidx;
    assert_valid_cidx (cidx);
    assert (!yals->lnk[cidx]);
    yals->lnk[cidx] = p;
    assert (!p->next || p->next == p + 1);
  }
  assert (free < c->lnks + size);
  yals->unsat.queue.nfree = (c->lnks + size) - free;
  assert (yals->unsat.queue.nfree > 0);
  prev = 0;
  for (p = c->lnks + size-1; p >= free; p--) p->next = prev, prev = p;
  yals->unsat.queue.free = free;
  assert (!c->next);
  yals->unsat.queue.chunks = c;
  yals->unsat.queue.nchunks = 1;
  yals->unsat.queue.nlnks = size - 1;
  assert (yals->stats.queue.max.lnks >= yals->unsat.queue.nlnks);
  assert (yals->stats.queue.max.chunks >= yals->unsat.queue.nchunks);
  yals->stats.time.defrag += yals_time (yals) - start;
}


static int yals_need_to_defrag_queue (Yals * yals) {
  if (!yals->opts.defrag.val) return 0;
  if (!yals->unsat.queue.count) return 0;
  if (yals->unsat.queue.nlnks <= yals->opts.minchunksize.val) return 0;
  if (yals->unsat.queue.count > yals->unsat.queue.nfree/4) return 0;
  return 1;
}

static void yals_dequeue_queue (Yals * yals, int cidx) {
  Lnk * l;
  assert (yals->unsat.usequeue);
  assert (yals->unsat.queue.count > 0);
  yals->unsat.queue.count--;
  l = yals->lnk[cidx];
 
  assert (l);
  assert (l->cidx == cidx);
  yals->lnk[cidx] = 0;
  yals_dequeue_lnk (yals, l);
  l->next = yals->unsat.queue.free;
  yals->unsat.queue.free = l;
  yals->unsat.queue.nfree++;
  assert (yals->unsat.queue.nlnks ==
          yals->unsat.queue.nfree + yals->unsat.queue.count);
  if (yals_need_to_defrag_queue (yals)) { yals_defrag_queue (yals);}
}

static inline void yals_dequeue_stack (Yals * yals, int cidx, int constraint_type) {
  int * pos = 0;
  UNSAT_STACK *unsat = 0;
  if (constraint_type == TYPECLAUSE) {
    if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
      unsat = &(yals->unsat_soft);
      pos = yals->pos_soft;
    }
    else {
      unsat = &(yals->unsat);
      pos = yals->pos;
    }
  } else if (constraint_type == TYPECARDINALITY) {
    if (yals->using_maxs_weights && !yals->hard_card_ids[cidx]) {
      unsat = &(yals->card_unsat_soft);
      pos = yals->card_pos_soft;
    }
    else {
      unsat = &(yals->card_unsat);
      pos = yals->card_pos;
    }
  } else {yals_abort (yals, "incorrect constraint type");}

  int cpos = pos[cidx], didx;
  assert (!unsat->usequeue);
  // // assert_valid_pos (cpos);
  assert (PEEK (unsat->stack, cpos) == cidx);
  didx = POP (unsat->stack);
  if (didx != cidx) {
    assert (pos[didx] == COUNT (unsat->stack));
    POKE (unsat->stack, cpos, didx);
    pos[didx] = cpos;
  }
  pos[cidx] = -1;
  
  if (yals->using_maxs_weights) { // remove weight from stack
    if (constraint_type == TYPECLAUSE)
      unsat->maxs_weight -= PEEK (yals->maxs_clause_weights, cidx);
    else if (constraint_type == TYPECARDINALITY)
      unsat->maxs_weight -= PEEK (yals->maxs_card_weights, cidx);
    else yals_abort (yals, "incorrect constraint type");
    
    assert (unsat->maxs_weight >= 0);
  }
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

static void yals_new_chunk (Yals * yals) {
  Lnk * p, * first, * prev = 0;
  Chunk * c;
  int size;
  size = yals->unsat.queue.chunksize;
  assert (size >= yals->opts.minchunksize.val);
  LOG ("new chunk of size %d", size);
  NEWN (p, size);
  c = (Chunk*) p;
  c->size = size;
  first = c->lnks + 1;
  for (p = c->lnks + size-1; p >= first; p--) p->next = prev, prev = p;
  yals->unsat.queue.nfree += size-1;
  yals->unsat.queue.free = first;
  c->next = yals->unsat.queue.chunks;
  yals->unsat.queue.chunks = c;
  yals->unsat.queue.nlnks += size - 1;
  if (yals->stats.queue.max.lnks < yals->unsat.queue.nlnks)
    yals->stats.queue.max.lnks = yals->unsat.queue.nlnks;
  if (yals->stats.queue.max.chunks < ++yals->unsat.queue.nchunks)
    yals->stats.queue.max.chunks = yals->unsat.queue.nchunks;
}

static void yals_larger_new_chunk (Yals * yals) {
  if (!yals->unsat.queue.chunksize)
    yals->unsat.queue.chunksize = yals->opts.minchunksize.val;
  else yals->unsat.queue.chunksize *= 2;
  yals_new_chunk (yals);
}

static Lnk * yals_new_lnk (Yals * yals) {
  Lnk * res = yals->unsat.queue.free;
  if (!res) {
    yals_larger_new_chunk (yals);
    res = yals->unsat.queue.free;
  }
  yals->unsat.queue.free = res->next;
  assert (yals->unsat.queue.nfree);
  yals->unsat.queue.nfree--;
  return res;
}

static void yals_enqueue_queue (Yals * yals, int cidx) {
  Lnk * res;
  assert (yals->unsat.usequeue);
  res = yals_new_lnk (yals);
  assert (!yals->lnk[cidx]);
  yals->lnk[cidx] = res;


  res->cidx = cidx;
  yals_enqueue_lnk (yals, res);
  yals->unsat.queue.count++;
  assert (yals->unsat.queue.count > 0);
  assert (yals->unsat.queue.nlnks ==
          yals->unsat.queue.nfree + yals->unsat.queue.count);
}

static inline void yals_enqueue_stack (Yals * yals, int cidx, int constraint_type) {
  int size;
  int * pos = 0;
  UNSAT_STACK *unsat = 0;
  if (constraint_type == TYPECLAUSE) {
    if (yals->using_maxs_weights && !yals->hard_clause_ids[cidx]) {
      unsat = &(yals->unsat_soft);
      pos = yals->pos_soft;
    }
    else {
      unsat = &(yals->unsat);
      pos = yals->pos;
    }
    if (yals->stats.maxstacksize < (size = SIZE (unsat->stack) + 1))
      yals->stats.maxstacksize = size;
  } else if (constraint_type == TYPECARDINALITY) {
    if (yals->using_maxs_weights && !yals->hard_card_ids[cidx]) {
      unsat = &(yals->card_unsat_soft);
      pos = yals->card_pos_soft;
    }
    else {
      unsat = &(yals->card_unsat);
      pos = yals->card_pos;
    }
    if (yals->stats.card_maxstacksize < (size = SIZE (unsat->stack) + 1))
      yals->stats.card_maxstacksize = size;
  } else {yals_abort (yals, "incorrect constraint type");}

  assert (!unsat->usequeue);
  assert (pos[cidx] < 0);
  pos[cidx] = COUNT (unsat->stack);
  PUSH (unsat->stack, cidx);
  if (yals->using_maxs_weights) { // add weight to stack
    if (constraint_type == TYPECLAUSE)
      unsat->maxs_weight += PEEK (yals->maxs_clause_weights, cidx);
    else if (constraint_type == TYPECARDINALITY)
      unsat->maxs_weight += PEEK (yals->maxs_card_weights, cidx);
    else yals_abort (yals, "incorrect constraint type");
  }
}

static inline void yals_enqueue (Yals * yals, int cidx, int constraint_type) {
  LOG ("enqueue %d", cidx);

  assert (!yals->unsat.usequeue);

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

static inline void yals_reset_unsat_soft_stack (Yals * yals) {
  assert (!yals->unsat_soft.usequeue);
  while (!EMPTY (yals->unsat_soft.stack)) {
    int cidx = POP (yals->unsat_soft.stack);
    assert (yals->pos_soft[cidx] == COUNT (yals->unsat_soft.stack));
    yals->pos_soft[cidx] = -1;
  }
  RELEASE (yals->unsat_soft.stack);
  yals->unsat_soft.maxs_weight = 0.0;
  yals->unsat_soft.hard_cnt = 0;

  // cardinality stack
  while (!EMPTY (yals->card_unsat_soft.stack)) {
    int cidx = POP (yals->card_unsat_soft.stack);
    assert (yals->card_pos_soft[cidx] == COUNT (yals->card_unsat_soft.stack));
    yals->card_pos_soft[cidx] = -1;
  }
  RELEASE (yals->card_unsat_soft.stack);
  yals->card_unsat_soft.maxs_weight = 0.0;
  yals->card_unsat_soft.hard_cnt = 0;
}

static inline void yals_reset_unsat_stack (Yals * yals) {
  assert (!yals->unsat.usequeue);
  while (!EMPTY (yals->unsat.stack)) {
    int cidx = POP (yals->unsat.stack);
    assert_valid_cidx (cidx);
    assert (yals->pos[cidx] == COUNT (yals->unsat.stack));
    yals->pos[cidx] = -1;
  }
  RELEASE (yals->unsat.stack);
  yals->unsat.maxs_weight = 0.0;
  yals->unsat.hard_cnt = 0;

  // cardinality stack
  while (!EMPTY (yals->card_unsat.stack)) {
    int cidx = POP (yals->card_unsat.stack);
    assert_valid_card_cidx (cidx);
    assert (yals->card_pos[cidx] == COUNT (yals->card_unsat.stack));
    yals->card_pos[cidx] = -1;
  }
  RELEASE (yals->card_unsat.stack);
  yals->card_unsat.maxs_weight = 0.0;
  yals->card_unsat.hard_cnt = 0;

  if (yals->using_maxs_weights) yals_reset_unsat_soft_stack (yals);
}


#endif