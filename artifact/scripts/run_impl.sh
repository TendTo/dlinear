#!/usr/bin/env bash
set -euo pipefail


readonly run_name=${1:-smoke}
readonly local_limit=${2:-6}
readonly solvers=(soplex qsoptex)
readonly iterations=(100 200 300)
readonly modes=("" "strict" "delta")
readonly instances_file="/instances/${run_name}.csv"
readonly common_args="--instances ${instances_file} --instances-prefix /benchmarks/ --skip-first-line --local-limit ${local_limit}"

echo "[artifact] Using benchmark listed in ${instances_file}"
echo "[artifact] Running smoke test"
cvc5 --version
echo "[artifact] Running cvc5 baseline"
echo "[artifact] Running cvc5"
python3 run_benchmarks.py cvc5 ${common_args} --output-dir /results
python3 result_parser.py cvc5 /results -o /results
echo "[artifact] Running glpk"
for iteration in "${iterations[@]}"; do
  echo "[artifact] Running glpk with ${iteration} iterations"
  python3 run_benchmarks.py glpk ${common_args} --output-dir /results/${iteration} --iterations ${iteration}
  python3 result_parser.py glpk /results/${iteration} -o /results
  for solver in "${solvers[@]}"; do
    for mode in "${modes[@]}"; do
      mode_args=""
      if [[ $mode == "strict" ]]; then
        mode_args="--strict"
      elif [[ $mode == "delta" ]]; then
        mode_args="--delta=0.00000001"
      fi
      echo "[artifact] Running ${solver} with ${iteration} iterations and mode ${mode}"
      python3 run_benchmarks.py ${solver} ${common_args} --output-dir /results/${iteration}/${mode} --iterations ${iteration} ${mode_args}
      python3 result_parser.py ${solver} /results/${iteration}/${mode} -o /results
    done
  done
done
echo "[artifact] Smoke test complete."
