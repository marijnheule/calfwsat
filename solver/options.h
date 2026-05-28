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
  OPT (breakzero,0,0,1,"always use break zero literal if possibe"); \
  OPT (cached,1,0,1,"use cached assignment during restart"); \
  OPT (cacheduni,0,0,1,"pick random cached assignment uniformly"); \
  OPT (cachemax,(1<<10),0,(1<<20),"max cache size of saved assignments"); \
  OPT (cachemin,1,0,(1<<10),"minimum cache size of saved assignments"); \
  OPT (clsselectp, 12 , 1, 100, "Clause selection probability for weight transfer in ddfw."); \
  OPT (csptmin, 10 , 1, 100, "cspt range minimum"); \
  OPT (csptmax, 20 , 20, 100, "cspt range maximum"); \
  OPT (computeneiinit,0 , 0, 1, "Compute the ddfw clause neighborhood initially for palsat"); \
  OPT (correct,0,0,1,"correct CB value depending on maximum length"); \
  OPT (crit,1,0,1,"dynamic break values (using critical lits)"); \
  OPT (cutoff,20000 , 0,INT_MAX,"flips per try (0 = unlimited; controls shared-cache cycle frequency)"); \
  OPT (ddfwpicklit, 2,1,6,"1=best,4=wrand"); \
  OPT (ddfwonly, 1,0,1,"1=only emply ddfw,0=employ a combination of heuristics"); \
  OPT (ddfwstartth, 10000,10,1000000,"use to compute threshold for #unsat_cluase/#total_clause to start ddfw."); \
  OPT (defrag,1,0,1,"defragemtation of unsat queue"); \
  OPT (fixed,4,0,INT_MAX,"fixed default strategy frequency (1=always)"); \
  OPT (geomfreq,66,0,100,"geometric picking first frequency (percent)"); \
  OPT (ignorewtcriteria,0,0,1,"ignore the check with initial weight while deciding a neighboring satisfied clause during weight transfer in ddfw"); \
  OPT (paramAsmall,5,1,100,"a>"); \
  OPT (paramAbig,10,1,100,"a="); \
  OPT (paramCSmall,1,1,8,"c>"); \
  OPT (paramCBig,2,1,8,"c="); \
  OPT (paramCeq,167,0,1000,"lw-ite additive term c (c = paramCeq/1000)"); \
  OPT (paramAeq,167,1,1000,"lw-ite multiplicative factor a (a = paramAeq/1000)"); \
  OPT (limofranda,25,0,1000,"limit for random value of a"); \
  OPT (hitlim,-1,-1,INT_MAX,"minimum hit limit"); \
  OPT (keep,0,0,1,"keep assignment during restart"); \
  OPT (maxtries,INT_MAX , 0,INT_MAX,"Maximum number of tries (default INT_MAX = unlimited)"); \
  OPT (minchunksize,(1<<8),2,(1<<20),"minium queue chunk size"); \
  OPT (pick,0,-1,4,"-1=pbfs,0=rnd,1=bfs,2=dfs,3=rbfs,4=ubfs"); \
  OPT (pol,0,-1,1,"negative=-1 positive=1 or random=0 polarity"); \
  OPT (prep,1,0,1,"preprocessing through unit propagation"); \
  OPT (rbfsrate,10,1,INT_MAX,"relaxed BFS rate"); \
  OPT (reluctant,1,0,1,"reluctant doubling of restart interval"); \
  OPT (restart,100000,0,INT_MAX,"basic (inner) restart interval"); \
  OPT (innerrestartoff, 1 ,0,1,"disable inner restart"); \
  OPT (restartouter,0,0,1,"enable restart outer"); \
  OPT (restartouterfactor,100,1,INT_MAX,"outer restart interval factor"); \
  OPT (setfpu,1,0,1,"set FPU to use double precision on Linux"); \
  OPT (sidewaysmove,1,0,1,"enable sideways move"); \
  OPT (stagrestart,0,0,1,"restart when ddfw is stagnent."); \
  OPT (stagrestartfact, 1000, 0, 2000,"stagnant research factor"); \
  OPT (termint,1000,0,INT_MAX,"termination call back check interval"); \
  OPT (threadspec, 0, 0, 1, "if true, a thread use a set of fixed parameter values (applicable to palsat)"); \
  OPT (toggleuniform,0,0,1,"toggle uniform strategy"); \
  OPT (unfairfreq,50,0,100,"unfair picking first frequency (percent)"); \
  OPT (uni,0,-1,1,"weighted=0,uni=1,antiuni=-1 clause weights"); \
  OPT (unipick,-1,-1,4,"clause picking strategy for uniform formulas"); \
  OPT (unirestarts,0,0,INT_MAX,"max number restarts for uniform formulas"); \
  OPT (urandp, 0,0,100,"urandom selection probability for urand+optimal for DDFW"); \
  OPT (verbose,0,0,5,"set verbose level"); \
  OPT (weight,5,1,8,"maximum clause weight"); \
  OPT (witness,1,0,1,"print witness"); \
  OPT (wpercentage,10,0,90,"percentage of clause weights to transfer."); \
  OPT (wtrule,2,1,6,"weight transfer rule"); \
  OPT (invwtfactor,1,1,100," factor for computing weight with the inv factor rule."); \
  OPT (wtrulelinchoice,3,1,10,"Linear weight transfer rule choice"); \
  OPT (card_wtrule,2,1,2,"card ddfw weight transfer rule (1: constant, 2: linear"); \
  OPT (card_compute,4,1,6,"card ddfw weight computation rule (1: linear, 2: exponential, 3: quadratic, 4: choice of exponent from option ddfw_cad_exp)"); \
  OPT (ddfw_neighbors_plus,0,0,1,"ddfw look for neighbors+ before random sat"); \
  OPT (maxs_hard_eps,0,0,INT_MAX,"pure maxsat hard epsilon"); \
  OPT (maxs_soft_eps,0,0,INT_MAX,"pure maxsat soft epsilon"); \
  OPT (maxs_soft_stochastic_selection,0,0,INT_MAX,"Soft Constraints: pick from top K variables with weighted stochastic selection"); \
  OPT (maxs_hard_stochastic_selection,7,0,INT_MAX,"All/Hard Constraints: pick from top K variables with weighted stochastic selection"); \
  OPT (init_solution,0,0,1,"start from initial solution provided at <init.sol> [currently only in (Pure) MaxSAT]"); \
  OPT (ddfw_init_clause_weight,100,1,INT_MAX,"initial ddfw clause weight"); \
  OPT (ddfw_init_card_weight,100,1,INT_MAX,"initial ddfw cardinality constraint weight"); \
  OPT (sat_ddfw_init_card_weight,100,1,INT_MAX,"initial ddfw cardinality constraint weight for SAT"); \
  OPT (maxs_transfer_soft,0,0,1,"transfer weight for soft constraints"); \
  OPT (maxs_soft_takes_hard,0,0,1,"soft constraints can take from hard in random transfer"); \
  OPT (maxs_hard_takes_soft,0,0,1,"hard constraints can take from soft in random transfer"); \
  OPT (wt_transfer_all,0,0,10,"transfer N / 10 of all weight on initial weight transfer"); \
  OPT (ddfw_card_exp,20,-INT_MAX,INT_MAX,"exp = <val> / 10 + 1 for card_compute=4"); \
  OPT (flip_gain_eps_e4,1000,0,INT_MAX,"if >0, snap |flip_gain| < val/10000 to 0 in basic_ddfw_score"); \
  OPT (maxs_transfer_slow,0,0,1,"transfer weights if no improvement on inner loop (slow), instead of every inner loop (fast)"); \
  OPT (ddfw_select_exp,1,1,INT_MAX,"exponent for weighting variable values in stochastic selection"); \
  OPT (ddfw_random_select,-1,-1,INT_MAX,"chance of selecting a literal from the stack at random during variable selection, N / 100000"); \
  OPT (maxs_outer_restart,0,0,INT_MAX,"flips before outer restart"); \
  OPT (maxs_inner_bound,1000,0,INT_MAX,"flips before inner bound increases"); \
  OPT (maxs_hit_bound,1,0,INT_MAX,"hits before inner restart (not technically a hit, just a non-improvement)"); \
  OPT (maxs_inner_mult,25,0,INT_MAX,"multiplier for hit bound and inner bound after hit bound is reached"); \
  OPT (maxs_flip_step,1,1,INT_MAX,"inner flips increment on each failed inner loop"); \
  OPT (maxs_pure,0,0,1,"set to pure (if adding partition units)"); \
  OPT (maxs_pure_polarity,0,-1,1,"set hard polarity (if adding partition units)"); \
  OPT (reset_weights_on_restart,0,0,1,"reset ddfw weights to initial values on inner restart"); \
  OPT (ddfw_maxs_init_weight_relative,1,0,1,"ddfw weights for soft constraints start as MaxSAT weights"); \
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