#!/bin/bash
readonly iterations=(100 200 300)
readonly solvers=(soplex qsoptex glpk)
readonly other_solvers=(cvc5 z3 yices)
readonly modes=("_strict" "_delta1e-08" "")
files=()

for iteration in "${iterations[@]}"; do
  for solver in "${solvers[@]}"; do
    for mode in "${modes[@]}"; do
        files+=( "Comet:comet_lfplpsmf/${solver}_i${iteration}${mode}.csv" )
    done
  done
done

for solver in "${other_solvers[@]}"; do
    files+=( "Comet:comet_lfplpsmf/${solver}.csv" )
done

scp ${files[@]} artifact/results/
