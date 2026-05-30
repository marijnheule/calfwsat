[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)


This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

Stochastic Local Search SAT Solver 
Weight-transfer algorithm with Native Support for Cardinality Constraints
===============================================================================

## check-sat

A checker for CNF/KNF/WKNF formulas and solutions.

Also has capabilities to partition a formula based on a BFS over neighboring constraints.

Extends code from benkiesl@ and jsreeves@ in [Cadical-proof-skeleton](https://code.amazon.com/packages/Cadical-proof-skeleton/trees/mainline)

# Build

```
cd tools/check-sat
g++ --std=c++11 check-sat.cpp -o check-sat
```

# Check

An assignment for a CNF/KNF/WKNF formula can be checked with the program `check-sat`.

This will also print the number of satisfied/unsatisfied clauses/cardinality constraints if the assignment is not a satisfying assignment.

The assignment format is a list of literals, e.g., `1 3 4 -5`. Any variable gaps in the assignment (`2` in the example) will be set to false.
 
`> ./check-sat <Formula> <ASSIGNMENT>`

# Convert between Formats

`> ./check-sat <Formula> -convert <file> -inputs_type <N> -output_type <M>`

The types are listed in an enum.

`TYPE {UNKNOWN,CNF,KNF,WCNF,WKNF,WCARD,CAI,LSECNF}`

The solver will parse CNF, KNF, WCNF, WKNF. 

WCARD, CAI and LSECNF need to be converted to a standard input type. These tyes come from related work and will likely not be relevant to users. We recommend writing formulas initially in WKNF to avoid a conversion. 