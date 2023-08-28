#!/bin/bash
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
readonly max_size=1000000

# Ensure that the folders exist
pushd "$script_path" > /dev/null
mkdir -p lp2
mkdir -p smt2
popd > /dev/null

pushd "$script_path/lp2" > /dev/null

# Download and unpack the LP benchmarks from http://old.sztaki.hu/~meszaros/public_ftp/lptestset/
if [ ! -f "emps.c" ]; then
    wget -r -np -nH --cut-dirs=2 -R index.html https://www.netlib.org/lp/data
    rm -r robots.txt readme *.gz *.f kennington changes
    # mv old.sztaki.hu/~meszaros/public_ftp/lptestset/* .
    # rm -rf old.sztaki.hu
fi


# Compile the emps program
if [ ! -f "emps" ]; then
    gcc -o emps emps.c
fi

for file in $(find . -not -name "emps*" -not -name "*.mps" -not -name "*.smt2" -type f); do
    echo "Decompressing file $file"
    if [ $(wc -c < "$file") -ge $max_size ]; then
        echo "Skipping $file because it is too large"
        continue
    fi
    mps_file="$(basename "$file").mps"
    ./emps -1 -b -m $file > $mps_file
    sed -ri 's/([0-9]+)\.$/\1/' $mps_file
    sed -ri 's/\.([0-9]+)$/0.\1/' $mps_file
    rm $file
done

for file in $(find . -name "*.mps"); do
    smt2_file=LP_$(basename "$file" .mps).smt2
    echo "Converting $file to SMT-LIB2 format..."
    toyconvert "$file" -o "$smt2_file" 2> /dev/null
    sed -i 's/(set-option :produce-models true)/(set-logic QF_LRA)/' "$smt2_file"
    sed -i 's/(!//' "$smt2_file"
    sed -i 's/ *:named[^)]*)//' "$smt2_file"
    # rm $file
    rm -f "toyconvert.tix"
done

popd > /dev/null

pushd "$script_path" > /dev/null

for file in $(find "$script_path/lp2" -name "*.smt2"); do
    mv "$file" "$script_path/smt2"
done

popd > /dev/null
