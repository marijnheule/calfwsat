#!/bin/sh

# remove executable (no-op: solver `make clean` below already removes binaries)
rm -f CaLFwSAT palsat

# clean solver
cd solver
make clean
cd ../

# clean tools
# cd tools
rm check-sat
