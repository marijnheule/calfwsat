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
  OPT (clsselectp, 15 , 0, 100, "Clause selection probability for weight transfer."); \
  OPT (topk,8,0,64,"per-literal top-K heaviest neighbors (0 = full scan)"); \
  OPT (cutoff,300000,0,INT_MAX,"flips per try (0 = unlimited)"); \
  OPT (dynmul,10,0,INT_MAX,"extend cutoff to D*probe-flips on improvement (0=off)"); \
  OPT (defrag,1,0,1,"defragemtation of unsat queue"); \
  OPT (slope,500,0,1000,"weight-transfer slope: w = slope/1000 * (source_weight - floor)"); \
  OPT (floor,80,0,INT_MAX,"weight-transfer floor: source weight where transfer = 0 (below it the source is skipped)"); \
  OPT (keep,0,0,1,"keep assignment during restart"); \
  OPT (maxtries,INT_MAX , 0,INT_MAX,"Maximum number of tries (default INT_MAX = unlimited)"); \
  OPT (pol,0,-1,1,"negative=-1 positive=1 or random=0 polarity"); \
  OPT (prep,1,0,1,"preprocessing through unit propagation"); \
  OPT (setfpu,1,0,1,"set FPU to use double precision on Linux"); \
  OPT (termint,1000,0,INT_MAX,"termination call back check interval"); \
  OPT (verbose,0,0,5,"set verbose level"); \
  OPT (witness,1,0,1,"print witness"); \
  OPT (card_compute,4,1,4,"card weight rule: 1=linear 2=exp 3=quadratic 4=cubic"); \
  OPT (init,100,1,INT_MAX,"initial clause/cardinality constraint weight"); \
  OPT (maxk,1,1,INT_MAX,"weight-transfer top-K sink sources (1 = single)"); \
  OPT (randk,1,0,INT_MAX,"random-source top-K sample size (0 = single random)"); \
  OPT (randtour,1,1,INT_MAX,"random-source tournament multiplier for --randk"); \
  OPT (wsamplepow,2,0,8,"random-source sampling exponent on weight (0 = uniform)"); \
  OPT (tabu,0,0,INT_MAX,"tabu length: skip N most-recent flips (0 = disabled)"); \
  OPT (age_window,10000,1,INT_MAX,"window size for avg_age stats"); \
  OPT (bypass,0,0,1,"probabilistically bypass inner restart at cutoff"); \
  OPT (heat,0,0,1,"track per-variable true-in-best counts; print at end"); \
  OPT (improving,0,0,1,"at restart keep assignment if best improved (0 = always re-pick)"); \
  OPT (oldestsource,1,0,1,"pick least-recently-used satisfied source (not random)"); \
  OPT (reset_os,1,0,1,"re-shuffle the oldestsource LRU order on each restart"); \
  OPT (flip_gain_eps_e4,1000,0,INT_MAX,"snap |flip_gain| < val/10000 to 0 (0 = off)"); \
  OPT (reset_weights,1,0,1,"reset weights to initial values on inner restart"); \
  OPT (wtstats,0,0,1,"print clause/card weight distribution at each probe end"); \
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
