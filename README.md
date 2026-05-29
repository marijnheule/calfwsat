## CaLFwSAT

_This software is only intended for development or test workloads, and you should not use it for production workloads._

A stochastic local search SAT Solver with native support for cardinality constraints based on the DDFW (divide and distribute fixed weights) algorithm.
DDFW is a stochastic local search (SLS) algorithm used for solving satisfiable formulas in propostional logic. The typical input for SLS solvers is conjunctive normal form (CNF), i.e., a conjunction of clauses, and each clause is a disjunction of literals. We extend the input format to accept a conjunction of clauses and cardinality constraints, e.g., a subset of pseudo-Boolean (PB) formulas, as well as weighted clauses and weighted constraints.

This solver was specifically developed for Pure Maximum Satisfiability (MaxSAT) optimization problems. These are problems with soft and hard constraints, where the soft constraints each have an associated cost. A solution to the problem must satsify all hard constraints. The cost of a solution is the sum of falsified soft constraints. The problem is Pure if the literals in the hard constraints all have the same polarity, and this is opposite the polarity of literals in the soft constraints.

The solver can be extended to general MaxSAT problems, but this is under development.

The solver will work for general SAT problems, but the default heuristics are not tuned for this class of problems.


This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [GitHub repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere), both under the MIT liscence.

## Build

build solver, `CaLFwSAT ` and checker `check-sat`

`> sh build.sh`

build with debugging: invariant checking, logging, and compiler warnings:

`> sh build.sh 1`

note, debugging mode will significantly slow down the solver on larger instances

## Clean

remove compiled files

`> sh clean.sh`

## Run with Checking

`> sh run.sh <Formula>`

With this script, the solution and solver information are deleted after checking.

## Run without Checking

`> ./CaLFwSAT -v --cutoff=<#flips> --maxtries=<#restarts> [--option=<val>] <Formula> [seed]`

To run with a timeout, try

`> timeout 100s ./CaLFwSAT -v --cutoff=<#flips> --maxtries=<#restarts> [--option=<val>] <Formula> [seed]`

The solver will catch the timeout signal and print the best cost solution to `witness.sol`.

Additional solver information will be printed to stdout.

## Start Solver with an Initial Assignment

`> ./CaLFwSAT -v --cutoff=<#flips> --maxtries=<#restarts> --init_solution=1 [--option=<val>] <Formula> [seed]`

Initial assignment should be placed in the file "init.sol".

The assignment should be formatted as a list of literals, e.g., `1 -2 3 4 -5`. Each line may start with a `v `.

## Checking

An assignment for a CNF/KNF/WKNF formula can be checked with the program `check-sat`.

This will also print the number of satisfied/unsatisfied clauses/cardinality constraints if the assignment is not a satisfying assignment.

The assignment format is a list of literals, e.g., `1 3 4 -5`. Any variable gaps in the assignment (`2` in the example) will be set to false.
 
`> ./check-sat <Formula> <ASSIGNMENT>`

## Small Tests

`> sh small-tests.sh`

Runs the solver and checker on a small magic squares 
and a small max squares KNF instance.

## KNF (at-least-K Conjunctive Normal Form)

A standard CNF header

`p knf <#Variables>  <#Klauses>`

Followed by a list of clauses and cardinality constriants.
A cardinality constraint is denoted by a `k` followed by a bound, then the list of literals. Cardinality constrainst are represented as at-least-k constraints.

A clause can be either represented as a cardinality constraint with bound 1, e.g., `k 1 -2 3 0`, or the `k 1` can be left off, e.g., `-2 3 0`. 

For example:

```
p knf 3 3
1 -2 0       c normal clause
k 2 1 2 -3 0 c X_1 + X_2 - X_3 >= 2
k 1 -2 3 0   c normal clause (could also be written: -2 3 0)
```

## WKNF (Weighted KNF)

A standard WCNF header

`p wknf <#Variables>  <#Klauses> <#Hard_Cost>`

Followed by a list of clauses and cardinality constriants.
A cardinality constraint is denoted by a `k` followed by a bound, then the list of literals. Cardinality constrainst are represented as at-least-k constraints.

Before each soft constraint is the integer cost.
Before each hard constraint is the hard cost.

For example:

```
p wknf 3 4 1000
1000 1 -2 0       c hard clause
1000 k 2 1 2 -3 0 c hard cardinality constraint X_1 + X_2 - X_3 >= 2
23 -2 3 0         c soft clause with cost 23
117 k 3 -1 2 -3 0 c soft cardinality constraint -X_1 + X_2 - X_3 >= 3 with cost 117
```

## Important Solver Options

Solver options are defaulted to work well with the middle mile benchmarks.
Below are a list of a few important options for tuning on new benchmarks.

Options with values:

`--card_compute=1` cardinality constraint ddfw weight computation rule (1: linear, 2: exponential, 3: quadratic, 4: choice of exponent). For SAT problems, exponential or quadratic may be better.

`--init_card_weight=35` the initial ddfw weight for cardinality constriants. This should change depending on the weight of soft constraints.

`--sat_ddfw_init_card_weight=8` the initial ddfw weight for cardinality constriants. This value is for SAT problems, not MaxSAT problems.

`--hard_stochastic_selection=7` All constraints (SAT) hard constraints (MaxSAT) make weighted random choice from top K variables with best ddfw weight changce. Set to 0/1 for picking best variable every time.

Pure MaxSAT specific:

`--maxs_inner_bound=1000` number of flips before a hit/updating exploration statistics. Increase for slower exploration.

`--maxs_hit_bound=1` number of hits before an inner restart. Increase for slower exploration.


Options that are on `1` or off `0`:

`--neighbors_plus=1` extends the definition of neighbor for problems with few neighbors like Middle Mile. For SAT problems, disabling this may be better.

`--reset_weights_on_restart=1` resets ddfw weights during a restart. For SAT problems, disabling this may be better.

# Debugging

To debug the solver, there are a few options:

`-l` : logging information to stdout

`-c` : checking invariants during runtime (extreme slowdown for large insatnces)

`--verbose=4` : additional information

There are also many assertions checked when compiling with debugging.

## Security

See [CONTRIBUTING](CONTRIBUTING.md#security-issue-notifications) for more information.

## License

This library is licensed under the MIT-0 License. See the LICENSE file.

