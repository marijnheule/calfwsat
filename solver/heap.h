/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and  mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the heap from the solver [kissat](https://github.com/arminbiere/kissat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _heap_h_INCLUDED
#define _heap_h_INCLUDED

#include "stack.h"

#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdlib.h>

#define DISCONTAIN UINT_MAX
#define DISCONTAINED(IDX) ((int) (IDX) < 0)

#define MAX(A,B) (((A) > (B)) ? (A) : (B))

typedef struct heap heap;

typedef STACK (unsigned) unsigneds;

struct Yals;

struct heap {
  bool tainted;
  unsigned vars;
  unsigned size;
  unsigneds stack;
  double *score;
  unsigned *pos;
};

struct Yals;

void yals_resize_heap (struct Yals *yals, heap *, unsigned size);

static inline bool yals_heap_contains (heap *heap, unsigned idx) {
  return idx < heap->vars && !DISCONTAINED (heap->pos[idx]);
}

static inline double yals_get_heap_score (const heap *heap,
                                            unsigned idx) {
  return idx < heap->vars ? heap->score[idx] : 0.0;
}

static inline bool yals_empty_heap (heap *heap) {
  return EMPTY (heap->stack);
}

void yals_enlarge_heap (struct Yals *yals,heap *, unsigned new_vars);

void yals_clear_heap (struct Yals *yals,heap *heap);

#ifndef NDEBUG
void yals_check_heap (heap *);
#else
#define yals_check_heap(...) \
  do { \
  } while (0)
#endif

#endif
