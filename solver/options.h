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
  OPT (topk,8,0,64,"per-literal top-K sorted list of heaviest neighbors (K=0 falls back to full scan)"); \
  OPT (cutoff,300000,0,INT_MAX,"flips per try (0 = unlimited; controls inner-restart frequency)"); \
  OPT (defrag,1,0,1,"defragemtation of unsat queue"); \
  OPT (fixed,1,0,INT_MAX,"fixed default strategy frequency (1=always)"); \
  OPT (wtadd,0,-1000,1000,"weight transfer additive term c (c = init_weight * wtadd/1000); negative subtracts from the transfer"); \
  OPT (wtmul,167,0,1000,"weight transfer multiplicative factor a (a = wtmul/1000)"); \
  OPT (wtpow,0,0,1000,"weight transfer power term; exponent p chosen so pow(init_weight,p) = init_weight*wtpow/1000 (0 disables term; 1000 = linear)"); \
  OPT (keep,0,0,1,"keep assignment during restart"); \
  OPT (maxtries,INT_MAX , 0,INT_MAX,"Maximum number of tries (default INT_MAX = unlimited)"); \
  OPT (minchunksize,(1<<8),2,(1<<20),"minium queue chunk size"); \
  OPT (pol,0,-1,1,"negative=-1 positive=1 or random=0 polarity"); \
  OPT (prep,1,0,1,"preprocessing through unit propagation"); \
  OPT (setfpu,1,0,1,"set FPU to use double precision on Linux"); \
  OPT (termint,1000,0,INT_MAX,"termination call back check interval"); \
  OPT (verbose,0,0,5,"set verbose level"); \
  OPT (witness,1,0,1,"print witness"); \
  OPT (card_compute,4,1,4,"cardinality constraint weight computation rule (1: linear c*d, 2: exponential c^d capped at d=7, 3: quadratic c*d^2, 4: cubic c*d^3)"); \
  OPT (init_clause_weight,100,1,INT_MAX,"initial clause weight"); \
  OPT (init_card_weight,100,1,INT_MAX,"initial cardinality constraint weight"); \
  OPT (wtini,0,0,1000,"if source still has exactly its initial weight, transfer initial_weight*wtini/1000 (instead of the linear rule)"); \
  OPT (min_weight,10,0,INT_MAX,"weight floor: no clause/card weight can drop below M. A source must have weight > M to be picked (otherwise it has no transfer headroom), and any transfer is capped at (source_weight - M) so the source ends up at exactly M in the worst case. M=0 = no floor (free transfer up to source_weight)."); \
  OPT (maxk,1,1,INT_MAX,"weight transfer top-K sources: for each falsified literal in the sink, find its best neighbor; aggregate up to N of those into the top k = min(N, #valid-per-literal-bests) and transfer from each, with each transfer amount divided by k. Same clause can appear multiple times if it's the per-literal best for multiple literals. N=1 (default) = current single-source behavior."); \
  OPT (randk,1,0,INT_MAX,"random-source top-K: when the random-source path is taken (clsselectp roll or max-weight fallback), instead of picking one random satisfied source, randomly sample R*K satisfied sources with weight > min-weight (R = --randtour), take the top K by weight, and transfer from each with amount/K. K=0 = original single-random behavior; K=1 (default) with randtour=1 (default) and wsamplepow=2 (default) = a single weight^2-proportional draw."); \
  OPT (randtour,1,1,INT_MAX,"random-source tournament size multiplier: when --randk=K>0, sample R*K satisfied sources before picking the top K by weight. Larger R biases the picked sources toward heavier ones at the cost of more rejection sampling per transfer. Default 1 (a single draw, no tournament -- the weight-proportional draw from --wsamplepow already biases toward heavy sources)."); \
  OPT (wsamplepow,2,0,8,"weighted-proportional random source sampling exponent p: draw each random-source candidate from a segment sum-tree with probability proportional to ddfw weight^p, instead of a uniform index. p=0 disables it (original uniform sampling); p=1 linear; p=2 (default) quadratic; higher p concentrates harder on heavy sources. SAT/min-weight/hard-soft are rejection-filtered at draw time, so the tree carries weight^p only and updates just 2 leaves per transfer. Only the draw distribution changes -- the transfer amount and top-K selection still use the linear weight."); \
  OPT (tabu,0,0,INT_MAX,"tabu length N: the N most-recently-flipped variables are skipped in the picker (0 = disabled)"); \
  OPT (age_window,10000,1,INT_MAX,"rolling window size for the avg_age/avg_hd statistics shown in 'new minimum' prints"); \
  OPT (hd_restart,0,0,INT_MAX,"trigger an inner restart when avg_hd drops below this threshold (0 = disabled; only fires once the K-flip window has filled)"); \
  OPT (bypass,1,0,1,"at cutoff, bypass with probability p = fraction of past probe-bests strictly worse than current stats.tmp; rolls a fresh dice on each subsequent cutoff hit"); \
  OPT (heat,1,0,1,"maintain a globally shared per-variable counter: at the end of each probe, increment heat[v] for every variable v that is true in the probe's best assignment; print all (var, count) pairs at end of run"); \
  OPT (improving,1,0,1,"at inner restart, if best strictly improved since the previous restart, keep the current assignment instead of re-picking (1 = default historical behavior; 0 = always re-pick regardless of improvement)"); \
  OPT (oldestsource,0,0,1,"random-source selection: instead of random, pick the satisfied source that has been least-recently used as a source (LRU)"); \
  OPT (sourcecap,500,0,1000,"cap per-transfer amount at source_weight*sourcecap/1000 (1000 = cap at source weight, the loosest binding; 0 = no transfer)"); \
  OPT (flip_gain_eps_e4,1000,0,INT_MAX,"if >0, snap |flip_gain| < val/10000 to 0 in basic score"); \
  OPT (random_select,-1,-1,INT_MAX,"chance of selecting a literal from the stack at random during variable selection, N / 100000"); \
  OPT (reset_weights_on_restart,0,0,1,"reset weights to initial values on inner restart"); \
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
