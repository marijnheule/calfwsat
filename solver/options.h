/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and manager Benjamin Kiesl (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

/*

  Options template for the solver.

  OPT (name, default, lowbound, upperbound, "description")

  when running the solver, use
  > ./solver --name=value 

  Default values are set for middle mile routing problems.

*/

#ifndef _options_h_INCLUDED
#define _options_h_INCLUDED


#define OPTSTEMPLATE \
  OPT (best,0,0,1,"always pick best assignment during restart"); \
  OPT (clsselectp, 12 , 1, 100, "Clause selection probability for weight transfer."); \
  OPT (topk,8,0,64,"per-literal top-K heaviest neighbors (0 = full scan)"); \
  OPT (cutoff,300000,0,INT_MAX,"flips per try (0 = unlimited)"); \
  OPT (defrag,1,0,1,"defragemtation of unsat queue"); \
  OPT (fixed,1,0,INT_MAX,"fixed default strategy frequency (1=always)"); \
  OPT (wtadd,0,-1000,1000,"weight-transfer additive term (init_weight*wtadd/1000)"); \
  OPT (wtmul,167,0,1000,"weight-transfer multiplicative factor (wtmul/1000)"); \
  OPT (wtpow,0,0,1000,"weight-transfer power term (0 = off, 1000 = linear)"); \
  OPT (keep,0,0,1,"keep assignment during restart"); \
  OPT (maxtries,INT_MAX , 0,INT_MAX,"Maximum number of tries (default INT_MAX = unlimited)"); \
  OPT (minchunksize,(1<<8),2,(1<<20),"minium queue chunk size"); \
  OPT (pol,0,-1,1,"negative=-1 positive=1 or random=0 polarity"); \
  OPT (prep,1,0,1,"preprocessing through unit propagation"); \
  OPT (setfpu,1,0,1,"set FPU to use double precision on Linux"); \
  OPT (termint,1000,0,INT_MAX,"termination call back check interval"); \
  OPT (verbose,0,0,5,"set verbose level"); \
  OPT (witness,1,0,1,"print witness"); \
  OPT (card_compute,4,1,4,"card weight rule: 1=linear 2=exp 3=quadratic 4=cubic"); \
  OPT (init_clause_weight,100,1,INT_MAX,"initial clause weight"); \
  OPT (init_card_weight,100,1,INT_MAX,"initial cardinality constraint weight"); \
  OPT (wtini,0,0,1000,"transfer for at-initial-weight sources (init_weight*wtini/1000)"); \
  OPT (min_weight,10,0,INT_MAX,"weight floor M for clauses/cards (0 = no floor)"); \
  OPT (maxk,1,1,INT_MAX,"weight-transfer top-K sink sources (1 = single)"); \
  OPT (randk,1,0,INT_MAX,"random-source top-K sample size (0 = single random)"); \
  OPT (randtour,1,1,INT_MAX,"random-source tournament multiplier for --randk"); \
  OPT (wsamplepow,2,0,8,"random-source sampling exponent on weight (0 = uniform)"); \
  OPT (tabu,0,0,INT_MAX,"tabu length: skip N most-recent flips (0 = disabled)"); \
  OPT (age_window,10000,1,INT_MAX,"window size for avg_age/avg_hd stats"); \
  OPT (hd_restart,0,0,INT_MAX,"inner restart when avg_hd below this (0 = disabled)"); \
  OPT (bypass,1,0,1,"probabilistically bypass inner restart at cutoff"); \
  OPT (heat,1,0,1,"track per-variable true-in-best counts; print at end"); \
  OPT (improving,1,0,1,"at restart keep assignment if best improved (0 = always re-pick)"); \
  OPT (oldestsource,0,0,1,"pick least-recently-used satisfied source (not random)"); \
  OPT (sourcecap,500,0,1000,"cap per-transfer at source_weight*sourcecap/1000"); \
  OPT (flip_gain_eps_e4,1000,0,INT_MAX,"snap |flip_gain| < val/10000 to 0 (0 = off)"); \
  OPT (random_select,-1,-1,INT_MAX,"random literal-pick chance N/100000 (-1 = off)"); \
  OPT (reset_weights,1,0,1,"reset weights to initial values on inner restart"); \
  OPTSTEMPLATENDEBUG

#ifndef NDEBUG
#define OPTSTEMPLATENDEBUG \
  OPT (logging, 0, 0, 1, "set logging level"); \
  OPT (checking, 0, 0, 1, "set checking level");
#else
#define OPTSTEMPLATENDEBUG
#endif

#define OPT(NAME,DEFAULT,MIN,MAX,DESCRIPTION) Opt NAME

#endif
