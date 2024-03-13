#!/bin/bash

# Run dlinear with Valgrind in order to detect memory leaks.
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
readonly root_dir="$script_path/.."
readonly files_path="$root_dir/test/solver/smt2/*.smt2"
readonly dlinear="$root_dir/bazel-bin/dlinear/dlinear"

function test_all() {
  echo "" > $root_dir/timeouts.txt
  for file in $files_path
  do
    echo "Processing $file file..."
    timeout 10 $dlinear -c --verbosity 10 $file 
    if [ $? -eq 124 ]; then
      echo "$file: Timeout occurred"
      echo "$file" >> $root_dir/timeouts.txt
    else
      echo "$file: No timeout"
    fi
  done
}

function test_instances() {
    echo "" > $root_dir/timeouts_instances.txt
    instances=("test/solver/smt2/bad_echos_ascend.base.smt2" 
        "test/solver/smt2/bad_echos_ascend.induction.smt2" 
        "test/solver/smt2/frame_prop.base.smt2" 
        "test/solver/smt2/frame_prop.induction.smt2" 
        "test/solver/smt2/gasburner-prop3-10.smt2"
        "test/solver/smt2/gasburner-prop3-8.smt2"
        "test/solver/smt2/gasburner-prop3-9.smt2"
        "test/solver/smt2/no_op_accs.base.smt2"
        "test/solver/smt2/pd_finish.base.smt2"
        "test/solver/smt2/pd_finish.induction.smt2"
        "test/solver/smt2/pd_no_op_accs.base.smt2"
        "test/solver/smt2/pursuit-safety-3.smt2"
        "test/solver/smt2/sc_init_frame_gap.induction.smt2"
    )

    for file in "${instances[@]}"
    do
    echo "Processing $file file..."
    timeout 10 $dlinear -c --verbosity 20 $file 
    if [ $? -eq 124 ]; then
        echo "$file: Timeout occurred"
        echo "$file" >> $root_dir/timeouts_instances.txt
    else
        echo "$file: No timeout"
    fi
    done
}

function get_smallest_file() {
    smallest_file=""
    smallest_size=1000000000
    for file in $files_path
    do
        size=$(wc -c <"$file")
        if [ $size -lt $smallest_size ]; then
            smallest_size=$size
            smallest_file=$file
        fi
    done
    echo "Smallest file: $smallest_file: $smallest_size bytes"
}

function get_smallest_file_instances() {
    smallest_file=""
    smallest_size=1000000000
    instances=("test/solver/smt2/bad_echos_ascend.base.smt2" 
        "test/solver/smt2/bad_echos_ascend.induction.smt2" 
        "test/solver/smt2/frame_prop.base.smt2" 
        "test/solver/smt2/frame_prop.induction.smt2" 
        "test/solver/smt2/gasburner-prop3-10.smt2"
        "test/solver/smt2/gasburner-prop3-8.smt2"
        "test/solver/smt2/gasburner-prop3-9.smt2"
        "test/solver/smt2/no_op_accs.base.smt2"
        "test/solver/smt2/pd_finish.base.smt2"
        "test/solver/smt2/pd_finish.induction.smt2"
        "test/solver/smt2/pd_no_op_accs.base.smt2"
        "test/solver/smt2/pursuit-safety-3.smt2"
        "test/solver/smt2/sc_init_frame_gap.induction.smt2"
    )
    for file in "${instances[@]}"
    do
        size=$(wc -c <"$file")
        if [ $size -lt $smallest_size ]; then
            smallest_size=$size
            smallest_file=$file
        fi
    done
    echo "Smallest file: $smallest_file: $smallest_size bytes"
}

get_smallest_file_instances