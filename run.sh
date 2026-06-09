#!/bin/sh

echo "\nRunning benchmark "$1
echo "\n"

./CaLFwSAT -v $1  > temp.log
cat temp.log

echo "\nChecking if assignment is correct"
./check-sat $1 witness.sol
rm temp.log witness.sol

echo "\n\n"
