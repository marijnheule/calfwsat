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
  OPT (cached,0,0,1,"use cached assignment during restart"); \
  OPT (cacheduni,0,0,1,"pick random cached assignment uniformly"); \
  OPT (cachemax,(1<<10),0,(1<<20),"max cache size of saved assignments"); \
  OPT (cachemin,1,0,(1<<10),"minimum cache size of saved assignments"); \
  OPT (clsselectp, 12 , 1, 100, "Clause selection probability for weight transfer."); \
  OPT (rndlit,0,0,1,"max-weight source selection: scan neighbors of only one randomly chosen falsified literal of the sink"); \
  OPT (topk,8,0,64,"per-literal top-K sorted list of heaviest neighbors (K=0 falls back to full scan)"); \
  OPT (cutoff,200000,0,INT_MAX,"flips per try (0 = unlimited; controls inner-restart and shared-cache cycle frequency)"); \
  OPT (defrag,1,0,1,"defragemtation of unsat queue"); \
  OPT (fixed,1,0,INT_MAX,"fixed default strategy frequency (1=always)"); \
  OPT (ignorewtcriteria,0,0,1,"ignore the check with initial weight while deciding a neighboring satisfied clause during weight transfer"); \
  OPT (wtadd,0,-1000,1000,"weight transfer additive term c (c = init_weight * wtadd/1000); negative subtracts from the transfer"); \
  OPT (wtmul,167,0,1000,"weight transfer multiplicative factor a (a = wtmul/1000)"); \
  OPT (wtpow,0,0,1000,"weight transfer power term; exponent p chosen so pow(init_weight,p) = init_weight*wtpow/1000 (0 disables term; 1000 = linear)"); \
  OPT (paramPos,1000,0,5000,"falsified-weight multiplier for positive constraints (pos = paramPos/1000)"); \
  OPT (componentlock,0,0,1,"restrict weight transfer to within shared-literal connected components"); \
  OPT (hitlim,-1,-1,INT_MAX,"minimum hit limit"); \
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
  OPT (neighbors_plus,0,0,1,"look for neighbors+ before random sat"); \
  OPT (maxs_hard_eps,0,0,INT_MAX,"pure maxsat hard epsilon"); \
  OPT (maxs_soft_eps,0,0,INT_MAX,"pure maxsat soft epsilon"); \
  OPT (maxs_soft_stochastic_selection,0,0,INT_MAX,"Soft Constraints: pick from top K variables with weighted stochastic selection"); \
  OPT (hard_stochastic_selection,1,0,INT_MAX,"All/Hard Constraints: pick from top K variables with weighted stochastic selection"); \
  OPT (init_solution,0,0,1,"start from initial solution provided at <init.sol> [currently only in (Pure) MaxSAT]"); \
  OPT (init_clause_weight,100,1,INT_MAX,"initial clause weight"); \
  OPT (init_card_weight,100,1,INT_MAX,"initial cardinality constraint weight"); \
  OPT (sat_ddfw_init_card_weight,100,1,INT_MAX,"initial cardinality constraint weight for SAT"); \
  OPT (maxs_transfer_soft,0,0,1,"transfer weight for soft constraints"); \
  OPT (maxs_soft_takes_hard,0,0,1,"soft constraints can take from hard in random transfer"); \
  OPT (maxs_hard_takes_soft,0,0,1,"hard constraints can take from soft in random transfer"); \
  OPT (wtini,0,0,1000,"if source still has exactly its initial weight, transfer initial_weight*wtini/1000 (instead of the linear rule)"); \
  OPT (suppress,1,0,1,"random-source selection: if 1 (default), require source to have weight >= initial weight; if 0, accept any satisfied source"); \
  OPT (tabu,0,0,INT_MAX,"tabu length N: the N most-recently-flipped variables are skipped in the picker (0 = disabled)"); \
  OPT (age_window,10000,1,INT_MAX,"rolling window size for the avg_age/avg_hd statistics shown in 'new minimum' prints"); \
  OPT (hd_restart,0,0,INT_MAX,"trigger an inner restart when avg_hd drops below this threshold (0 = disabled; only fires once the K-flip window has filled)"); \
  OPT (cutoff_bypass,0,0,1,"at cutoff, bypass with probability p = fraction of past probe-bests strictly worse than current stats.tmp; rolls a fresh dice on each subsequent cutoff hit"); \
  OPT (oldestsource,0,0,1,"random-source selection: instead of random, pick the satisfied source that has been least-recently used as a source (LRU)"); \
  OPT (sourcecap,500,0,1000,"cap per-transfer amount at source_weight*sourcecap/1000 (1000 = cap at source weight, the loosest binding; 0 = no transfer)"); \
  OPT (flip_gain_eps_e4,1000,0,INT_MAX,"if >0, snap |flip_gain| < val/10000 to 0 in basic score"); \
  OPT (maxs_transfer_slow,0,0,1,"transfer weights if no improvement on inner loop (slow), instead of every inner loop (fast)"); \
  OPT (select_exp,1,1,INT_MAX,"exponent for weighting variable values in stochastic selection"); \
  OPT (random_select,-1,-1,INT_MAX,"chance of selecting a literal from the stack at random during variable selection, N / 100000"); \
  OPT (maxs_outer_restart,0,0,INT_MAX,"flips before outer restart"); \
  OPT (maxs_inner_bound,1000,0,INT_MAX,"flips before inner bound increases"); \
  OPT (maxs_hit_bound,1,0,INT_MAX,"hits before inner restart (not technically a hit, just a non-improvement)"); \
  OPT (maxs_inner_mult,25,0,INT_MAX,"multiplier for hit bound and inner bound after hit bound is reached"); \
  OPT (maxs_flip_step,1,1,INT_MAX,"inner flips increment on each failed inner loop"); \
  OPT (maxs_pure,0,0,1,"set to pure (if adding partition units)"); \
  OPT (maxs_pure_polarity,0,-1,1,"set hard polarity (if adding partition units)"); \
  OPT (reset_weights_on_restart,0,0,1,"reset weights to initial values on inner restart"); \
  OPT (maxs_init_weight_relative,1,0,1,"weights for soft constraints start as MaxSAT weights"); \
  OPT (maxs_keep_assignment,-1,-1,INT_MAX,"chance of keeping the current assignment after an inner restart, N / 100000"); \
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