# scp Comet:comet_lfplpsmf/soplex_i100.csv Comet:comet_lfplpsmf/soplex_i200.csv Comet:comet_lfplpsmf/cvc5.csv Comet:comet_lfplpsmf/glpk_i200.csv Comet:comet_lfplpsmf/z3.csv Comet:comet_lfplpsmf/yices.csv Comet:comet_lfplpsmf/soplex_i200_strict.csv Comet:comet_lfplpsmf/qsoptex_i100.csv Comet:comet_lfplpsmf/qsoptex_i100_strict.csv Comet:comet_lfplpsmf/qsoptex_i200.csv  Comet:comet_lfplpsmf/qsoptex_i200_strict.csv  .

# scp CometRemote:comet_lfplpsmf/soplex_i100.csv CometRemote:comet_lfplpsmf/soplex_i200.csv CometRemote:comet_lfplpsmf/cvc5.csv CometRemote:comet_lfplpsmf/glpk_i200.csv CometRemote:comet_lfplpsmf/z3.csv CometRemote:comet_lfplpsmf/yices.csv CometRemote:comet_lfplpsmf/soplex_i200_strict.csv CometRemote:comet_lfplpsmf/qsoptex_i100.csv CometRemote:comet_lfplpsmf/qsoptex_i100_strict.csv CometRemote:comet_lfplpsmf/qsoptex_i200.csv  CometRemote:comet_lfplpsmf/qsoptex_i200_strict.csv  .



readonly iterations=(100 200 300)
readonly solvers=(soplex qsoptex glpk)
readonly modes=(_strict _delta1e-08 "")
files=()

for iteration in "${iterations[@]}"; do
  for solver in "${solvers[@]}"; do
    for mode in "${modes[@]}"; do
        files+=( "Comet:comet_lfplpsmf/${solver}_i${iteration}${mode}.csv" )
    done
  done
done

scp ${files[@]} .