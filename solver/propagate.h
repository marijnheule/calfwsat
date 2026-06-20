/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

#ifndef _propagate_h_INCLUDED
#define _propagate_h_INCLUDED

#include "yals.h"
#include "yils_card.h"
#include "invariants.h"
#include "stack.h"

/*

  Propagate units and remove satisfied/falsified literals from constraints.

  A cardinality constraint is unit if the number of falsified literals = size - bound,
  then remaining literals are propagated as true.

  A cardinality constraint requires bound + 1 literal watch pointers during propagation.

  When removing satisifed literals from a cardinality constraint, decrement the bound.

  A falsified constraint during propagation means the formula is unsatisfiable.

*/

void yals_preprocess (Yals * yals) {
  int nvars = yals->nvars, lit, other, next, occ, w0, w1;
  int * p, * c, * q, oldnlits, newnlits, satisfied, nsat, nstr;
  STACK(int) * watches, * s;
  signed char * vals;
  int len;

  // cardinality constraint handling
  STACK(int) * card_watches, *s1;
  int bound, nWatches, temp_iter;
  int *temp_c, *watched_lit_pos;
  int curr_len;

  FIT (yals->f->cdb);

  NEWN (vals, 2*nvars);
  vals += nvars;

  NEWN (watches, 2*nvars);
  watches += nvars; // put pointer into middle of stack so you can directly index negative literals
  int cls_cnt = 0;
  for (c = yals->f->cdb.start; c < yals->f->cdb.top; c++) {
    
    occ = c - yals->f->cdb.start;
    assert (occ >= 0);
    if (!(w0 = *c)) continue;
    if (!(w1 = *++c)) continue;
    LOGLITS (c - 1, "watching %d and %d in", w0, w1);
    PUSH (watches[w0], occ);
    PUSH (watches[w1], occ);
    while (*++c)
      ;
    cls_cnt++;
  }

  // cardinality constraint watches
  FIT (yals->card_cdb);

  NEWN (card_watches, 2*nvars);
  card_watches += nvars;

  c = yals->card_cdb.start;
  cls_cnt = 0;
  while (c < yals->card_cdb.top) {

    occ = c - yals->card_cdb.start;
    bound = *c++;
    assert (bound > 0);
    len = 0;
    while (*c++) len++;
    if (len == bound) continue; // unit cardinality constraint (propagated during parsing)
    c -= len;
    c--;
    nWatches = bound+1; // watch bound+1 literals in constraint
    LOGLITS (c-1, "watching first %d literals with length %d and bound %d", nWatches, len, bound);
    for (temp_iter = 0; temp_iter < nWatches; temp_iter++) {
      assert (*c);
      PUSH (card_watches[*c], occ);
      LOGLITS (c-temp_iter-1, "Watch %d watching %d", temp_iter, *c);
      c++;
    }
    
    while (*c) // proceed until 0 (end of clause)
      ++c;
    ++c; // move on to next bound
    cls_cnt++;
  }

  // constraint propagation outer loop: loop over assigned literals
  for (next = 0; !yals->mt && next < COUNT (yals->trail); next++) {
    lit = PEEK (yals->trail, next);
    LOG ("propagating %d", lit);
    if (vals[lit] > 0) continue;
    if (vals[lit] < 0) {
      LOG ("inconsistent units %d and %d", -lit, lit);
      yals->mt = 1;
    } else {
      assert (!vals[lit]);
      vals[lit] = 1;
      assert (!vals[-lit]);
      vals[-lit] = -1;

      // contraint propagation inner loop: propagate lit

      // propagate over clause watches
      s = watches - lit;
      for (p = s->start; !yals->mt && p < s->top; p++) {
        occ = *p;
        assert (occ >= 0);
        c = yals->f->cdb.start + occ;
        assert (c < yals->f->cdb.top);
        if (c[1] != -lit) SWAP (int, c[0], c[1]);
        assert (c[1] == -lit);
        if (vals[w0 = c[0]] > 0) continue;
        for (q = c + 2; (other = *q); q++)
        if (vals[other] >= 0) break;
        if (other) {
        SWAP (int, c[1], *q);
        LOGLITS (c, "watching %d instead of %d in", other, lit);
        PUSH (watches[other], occ);
        } else if (!vals[w0]) {
        LOGLITS (c, "found new unit %d in", w0);
        PUSH (yals->trail, w0);
        } else {
        assert (vals[w0] < 0);
        LOGLITS (c, "found inconsistent");
        yals->mt = 1;
        }
      }
      RELEASE (*s);

      // propagate over cardinality constraint watches
      s1 = card_watches - lit;
      for (p = s1->start; !yals->mt && p < s1->top; p++) {
        occ = *p;
        assert (occ >= 0);
        c = yals->card_cdb.start + occ;
        assert (c < yals->card_cdb.top);
        bound = *c++;
        nWatches = bound+1;
        assert (bound > 0);

        LOGLITS (c-1, "Checking lit %d, nwatches %d with bound %d", -lit, nWatches, bound);

        // find watched literal in cardinality constraint
        watched_lit_pos = NULL;
        for (temp_c = c; *temp_c; temp_c++) {
          if (*temp_c == -lit) {watched_lit_pos = temp_c; break;}
        }
        assert (watched_lit_pos != NULL);

        // find satisifed or unassigned literal (after watched literals)
        for (q = c + nWatches; (other = *q); q++)
          if (vals[other] >= 0) break;

        if (other) { // found new literal to swap
          SWAP (int, *watched_lit_pos, *q);
          PUSH (card_watches[other], occ);
          LOGLITS (c, "watching %d instead of %d in", other, -lit);
        } else { // try propagating units (all but one watched literals)
          temp_c = c;
          for (temp_iter = 0; temp_iter < nWatches; temp_iter++) {
            if (*temp_c != -lit) {
              if (!vals[*temp_c]) PUSH (yals->trail, *temp_c);
              else if (vals[*temp_c] < 0) {
                LOGLITS (c, "found inconsistent, on lit %d", *temp_c);
                yals->mt = 1;
                break;
              }
            }
            temp_c++;
          }
        }
      }
      RELEASE (*s1);

    }
  }
  FIT (yals->trail);
  yals_msg (yals,2,
    "found %d units during unit propagation",
    COUNT (yals->trail));

  for (lit = -nvars; lit < nvars; lit++) RELEASE (watches[lit]);
  watches -= nvars;
  DELN (watches, 2*nvars);
  oldnlits = COUNT (yals->f->cdb);

  // free card_watches
  for (lit = -nvars; lit < nvars; lit++) RELEASE (card_watches[lit]);
  card_watches -= nvars;
  DELN (card_watches, 2*nvars);

  if (yals->mt) goto DONE;

  // reduce clause literals
  cls_cnt = 0; 
  int curr_cnt = 0;
  nstr = nsat = 0;
  int cls_size = 0;
  int falsified = 0;
  q = yals->f->cdb.start;
  for (c = q; c < yals->f->cdb.top; c++) {
    satisfied = 0;
    for (p = c; (lit = *p); p++)
      if (vals[lit] > 0) satisfied = 1;
    if (!satisfied) {
      for (p = c; (lit = *p); p++) {
        if (vals[lit] < 0) continue;
        assert (!vals[lit]);
        *q++ = lit;
        nstr++;
        cls_size++;
      }
      if (!cls_size) {

        // a fully falsified hard clause is the empty clause: formula is UNSAT
        yals->mt = 1;
        falsified++;

      } else {

        assert (satisfied || cls_size);
        cls_size = 0;
        assert (q >= yals->f->cdb.start + 1);
        assert (q[-1]); //assert (q[-2]); // may be units
        *q++ = 0;
      }
    } else { // satisfied clause
      nsat++;
      // want to tabulate this weight? (only if we care about weight of satisfied constraints)
    }
    c = p;
    cls_cnt++;
  }

  yals->f->cdb.top = q;
  FIT (yals->f->cdb);
  newnlits = COUNT (yals->f->cdb);
  assert (newnlits <= oldnlits);
  yals_msg (yals, 1, "removed %d satisfied clauses", nsat);
  yals_msg (yals, 1, "removed %d falsified clauses", falsified);
  yals_msg (yals, 1, "removed %d falsified literal occurrences", nstr);
  yals_msg (yals, 1,
    "literal stack reduced by %d to %d from% d",
    oldnlits - newnlits, newnlits, oldnlits);


  // reduce cardinality constraint literals
  cls_cnt = curr_cnt = 0;
  oldnlits = COUNT (yals->card_cdb);
  nstr = nsat = falsified = 0;
  q = yals->card_cdb.start;
  for (c = q; c < yals->card_cdb.top; c++) {
    satisfied = 0;
    bound = *c++;
    curr_len = 0;
    for (p = c; (lit = *p); p++)
      if (vals[lit] > 0) satisfied++;
    if (satisfied < bound) {

      *q++ = bound-satisfied; // new bound after removing sat liteals
      for (p = c; (lit = *p); p++) {
        if (vals[lit]) continue; // lit is assigned
        assert (!vals[lit]);
        *q++ = lit;
        nstr++;
        curr_len++;
      }
      LOG ("bound %d satisfied %d nstr %d", bound, satisfied, curr_len);

      assert (bound-satisfied < curr_len); // hard constraints cannot be falsified
      assert (q >= yals->card_cdb.start + 2);
      assert (q[-1]); assert (q[-2]);
      *q++ = 0;
    } else {
      // want to tabulate this weight? (only if we care about weight of satisfied constraints)
      nsat++; // satisfied cardinality constraint
    }
    c = p;
    cls_cnt++;
  }
  yals->card_cdb.top = q;
  FIT (yals->card_cdb);
  newnlits = COUNT (yals->card_cdb);
  assert (newnlits <= oldnlits);
  yals_msg (yals, 1, "removed %d satisfied cardinality constraints", nsat);
  yals_msg (yals, 1, "removed %d falsified literal occurrences", nstr);
  yals_msg (yals, 1,
    "literal stack reduced by %d to %d from% d",
    oldnlits - newnlits, newnlits, oldnlits);

DONE:
 
  vals -= nvars;
  DELN (vals, 2*nvars);
}



#endif