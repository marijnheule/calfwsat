/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the heap from the solver [kissat](https://github.com/arminbiere/kissat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _inlineheap_h_INCLUDED
#define _inlineheap_h_INCLUDED

#include "stack.h"
#include "heap.h"
#include "yals.h"

#define HEAP_CHILD(POS) (assert ((POS) < (1u << 31)), (2 * (POS) + 1))

#define HEAP_PARENT(POS) (assert ((POS) > 0), (((POS) -1) / 2))

static inline void yals_bubble_up (Yals *yals, heap *heap,
                                     unsigned idx) {
  unsigned *stack = BEGIN (heap->stack);
  unsigned *pos = heap->pos;
  unsigned idx_pos = pos[idx];
  const double *const score = heap->score;
  const double idx_score = score[idx];
  while (idx_pos) {
    const unsigned parent_pos = HEAP_PARENT (idx_pos);
    const unsigned parent = stack[parent_pos];
    if (score[parent] >= idx_score)
      break;
    LOG ("heap bubble up: %u@%u = %g swapped with %u@%u = %g", parent,
         parent_pos, score[parent], idx, idx_pos, idx_score);
    stack[idx_pos] = parent;
    pos[parent] = idx_pos;
    idx_pos = parent_pos;
  }
  stack[idx_pos] = idx;
  pos[idx] = idx_pos;
}

static inline void yals_bubble_down (Yals *yals, heap *heap,
                                       unsigned idx) {
  unsigned *stack = BEGIN (heap->stack);
  const unsigned end = COUNT (heap->stack);
  unsigned *pos = heap->pos;
  unsigned idx_pos = pos[idx];
  const double *const score = heap->score;
  const double idx_score = score[idx];
  for (;;) {
    unsigned child_pos = HEAP_CHILD (idx_pos);
    if (child_pos >= end)
      break;
    unsigned child = stack[child_pos];
    double child_score = score[child];
    const unsigned sibling_pos = child_pos + 1;
    if (sibling_pos < end) {
      const unsigned sibling = stack[sibling_pos];
      const double sibling_score = score[sibling];
      if (sibling_score > child_score) {
        child = sibling;
        child_pos = sibling_pos;
        child_score = sibling_score;
      }
    }
    if (child_score <= idx_score)
      break;
    LOG ("heap bubble down: %u@%u = %g swapped with %u@%u = %g", child,
         child_pos, score[child], idx, idx_pos, idx_score);
    stack[idx_pos] = child;
    pos[child] = idx_pos;
    idx_pos = child_pos;
  }
  stack[idx_pos] = idx;
  pos[idx] = idx_pos;
}

#define HEAP_IMPORT(IDX) \
  do { \
    assert ((IDX) < UINT_MAX - 1); \
    if (heap->vars <= (IDX)) \
      yals_enlarge_heap (yals, heap, (IDX) + 1); \
  } while (0)

static inline void yals_push_heap (Yals *yals, heap *heap,
                                     unsigned idx) {
  LOG ("push heap %u", idx);
  assert (!yals_heap_contains (heap, idx));
  HEAP_IMPORT (idx);
  heap->pos[idx] = COUNT (heap->stack);
  PUSH (heap->stack, idx);
  yals_bubble_up (yals, heap, idx);
  yals_bubble_down (yals, heap, idx);
}

static inline void yals_pop_heap (Yals *yals, heap *heap,
                                    unsigned idx) {
  LOG ("pop heap %u, position %u, size %u", idx, heap->pos[idx], COUNT (heap->stack));
  assert (yals_heap_contains (heap, idx));
  if (idx != PEEK (heap->stack, heap->pos[idx])) {
    yals_msg (yals, 1, "pop heap %u, position %u, size %u", idx, heap->pos[idx], COUNT (heap->stack));
    yals_msg (yals, 1, "%u actually at %u", PEEK (heap->stack, heap->pos[idx]), heap->pos[idx]);
  }
  assert (idx == PEEK (heap->stack, heap->pos[idx]));
  const unsigned last = POP (heap->stack);
  heap->pos[last] = DISCONTAIN;
  if (last == idx)
    return;
  const unsigned idx_pos = heap->pos[idx];
  heap->pos[idx] = DISCONTAIN;
  if (!((idx_pos) < COUNT(heap->stack))) {
    yals_msg (yals, 1, "pop heap %u, position %u, int %d, size %u, last %u", idx, idx_pos, (int) idx_pos, COUNT (heap->stack), last);
  }
  POKE (heap->stack, idx_pos, last);
  heap->pos[last] = idx_pos;
  yals_bubble_up (yals, heap, last);
  yals_bubble_down (yals, heap, last);
#ifdef CHECK_HEAP
  yals_check_heap (heap);
#endif
}

static inline unsigned yals_pop_max_heap (Yals *yals, heap *heap) {
  assert (!EMPTY (heap->stack));
  unsigneds *stack = &heap->stack;
  unsigned *const begin = BEGIN (*stack);
  const unsigned idx = *begin;
  assert (!heap->pos[idx]);
  LOG ("pop max heap %u", idx);
  const unsigned last = POP (*stack);
  unsigned *const pos = heap->pos;
  pos[last] = DISCONTAIN;
  if (last == idx)
    return idx;
  pos[idx] = DISCONTAIN;
  *begin = last;
  pos[last] = 0;
  yals_bubble_down (yals, heap, last);
#ifdef CHECK_HEAP
  yals_check_heap (heap);
#endif
  return idx;
}

static inline void yals_update_heap (Yals *yals, heap *heap,
                                       unsigned idx, double new_score) {
  if (!yals_heap_contains (heap, idx)) {
    yals_push_heap (yals, heap, idx);
  }
  const double old_score = yals_get_heap_score (heap, idx);
  if (old_score == new_score)
    return;
  HEAP_IMPORT (idx);
  LOG ("update heap %u score from %g to %g", idx, old_score, new_score);
  heap->score[idx] = new_score;
  if (!heap->tainted) {
    heap->tainted = true;
    LOG ("tainted heap");
  }
  // if (new_score > old_score)
    yals_bubble_up (yals, heap, idx);
  // else
    yals_bubble_down (yals, heap, idx);
#ifdef CHECK_HEAP
  yals_check_heap (heap);
#endif
}

void yals_release_heap (Yals *yals,heap *heap) {
  RELEASE (heap->stack);
  DELN (heap->pos, heap->size);
  DELN (heap->score, heap->size);
  memset (heap, 0, sizeof *heap);
}

#ifndef NDEBUG

void yals_check_heap (heap *heap) {
  const unsigned *const stack = BEGIN (heap->stack);
  const unsigned end = COUNT (heap->stack);
  const unsigned *const pos = heap->pos;
  const double *const score = heap->score;
  for (unsigned i = 0; i < end; i++) {
    const unsigned idx = stack[i];
    const unsigned idx_pos = pos[idx];
    assert (idx_pos == i);
    unsigned child_pos = HEAP_CHILD (idx_pos);
    unsigned parent_pos = HEAP_PARENT (child_pos);
    assert (parent_pos == idx_pos);
    if (child_pos < end) {
      unsigned child = stack[child_pos];
      printf ("score, idx, pos %lf %u %u score child %lf %u %u\n",score[idx],idx, idx_pos,score[child], child, child_pos);
      assert (score[idx] >= score[child]);
      if (++child_pos < end) {
        parent_pos = HEAP_PARENT (child_pos);
        assert (parent_pos == idx_pos);
        child = stack[child_pos];
        assert (score[idx] >= score[child]);
      }
    }
  }
}

#endif

void yals_resize_heap (Yals *yals,heap *heap, unsigned new_size) {
  const unsigned old_size = heap->size;
  if (old_size >= new_size)
    return;
  LOG ("resizing %s heap from %u to %u",
       (heap->tainted ? "tainted" : "untainted"), old_size, new_size);

  heap->pos = yals_realloc (yals, heap->pos, old_size*sizeof (unsigned), new_size*sizeof (unsigned));
  if (heap->tainted) {
    heap->score = yals_realloc (yals, heap->score, old_size*sizeof (double), new_size*sizeof (double));
  } else {
    if (old_size)
      DELN (heap->score, old_size);
    heap->score = yals_malloc (yals, new_size * sizeof (double));
  }
  heap->size = new_size;
#ifdef CHECK_HEAP
  yals_check_heap (heap);
#endif
}

void yals_rescale_heap (Yals *yals,heap *heap, double factor) {
  LOG ("rescaling scores on heap with factor %g", factor);
  double *score = heap->score;
  for (unsigned i = 0; i < heap->vars; i++)
    score[i] *= factor;
#ifndef NDEBUG
  yals_check_heap (heap);
#endif
}

void yals_enlarge_heap (Yals *yals,heap *heap, unsigned new_vars) {
  const unsigned old_vars = heap->vars;
  assert (old_vars < new_vars);
  assert (new_vars <= heap->size);
  const size_t delta = new_vars - heap->vars;
  for (int i = old_vars; i < delta + old_vars; i++) {
    heap->pos[i] = DISCONTAIN;
    heap->score[i] = 0.0;
  }
  heap->vars = new_vars;
  // if (heap->tainted)
  LOG ("enlarged heap from %u to %u", old_vars, new_vars);
}

void yals_clear_heap (Yals *yals,heap *heap) {
  while (!yals_empty_heap (heap))
    yals_pop_max_heap (yals, heap);
}

#ifndef NDEBUG

static void dump_heap (heap *heap) {
  for (unsigned i = 0; i < SIZE (heap->stack); i++)
    printf ("heap.stack[%u] = %u\n", i, PEEK (heap->stack, i));
  for (unsigned i = 0; i < heap->vars; i++)
    printf ("heap.pos[%u] = %u\n", i, heap->pos[i]);
  for (unsigned i = 0; i < heap->vars; i++)
    printf ("heap.score[%u] = %g\n", i, heap->score[i]);
}

void yals_dump_heap (heap *heap) { dump_heap (heap); }


#endif
#endif
