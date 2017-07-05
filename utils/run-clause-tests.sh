#!/bin/bash
# Reads configs from a file
# num_vars num_clauses neg_prob clause_size name
make
make -C ../ release
mkdir -p tests
rm tests/*
cp $1 tests/
cd tests
touch result
ulimit -t 60
while read p; do
  filename=`echo $p | awk '{print $5}'`

  if [[ "${p:0:1}" == "#" ]]; then
    continue
  fi

  # echo $p
  echo $filename
  ../gen-targetted-clauses $p "po"
  t=`(time ../../z3.out.release $filename) 2>&1 >/dev/null | grep 'real' | awk '{print $2}'`
  echo "PO: " $t $filename >> result
  cp $filename po-$filename

  ../gen-targetted-clauses $p "lo"
  t=`(time ../../z3.out.release $filename) 2>&1 >/dev/null | grep 'real' | awk '{print $2}'`
  echo "LO: " $t $filename >> result
  cp $filename lo-$filename

  ../gen-targetted-clauses $p "idl"
  t=`(time ../../z3.out.release $filename) 2>&1 >/dev/null | grep 'real' | awk '{print $2}'`
  echo "IDL: " $t $filename >> result
done < `basename $1`