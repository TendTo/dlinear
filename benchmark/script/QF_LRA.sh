#!/bin/bash
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"

pushd "$script_path" > /dev/null
git clone https://clc-gitlab.cs.uiowa.edu:2443/SMT-LIB-benchmarks/QF_LRA.git
mkdir -p smt2
# find all *.smt2 files in QF_LRA and move them to the smt2 folder, adding the prefix QF_LRA_
for file in $(find QF_LRA -name "*.smt2"); do
    cp $file smt2/QF_LRA_$(basename $file)
done
rm -rf QF_LRA
popd > /dev/null