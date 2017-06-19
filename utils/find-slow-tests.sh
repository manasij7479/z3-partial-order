#!/bin/bash
rm -rf tests
num_tests=100
num_vars=10000
num_pos=30000
num_neg=10000
python generate-many.py $num_tests $num_vars $num_pos $num_neg
./run-all-and-sort.sh tests ../z3/buildd/z3
cat result | more
