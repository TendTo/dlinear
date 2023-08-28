#!/bin/bash
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
readonly max_size=1000000

# Ensure that the folders exist
pushd "$script_path" > /dev/null || exit
mkdir -p lp
mkdir -p smt2
popd > /dev/null || exit

pushd "$script_path/lp" > /dev/null || exit

# Download and unpack the LP benchmarks from http://old.sztaki.hu/~meszaros/public_ftp/lptestset/
if [ ! -f "emps.c" ]; then
    wget -m -np http://old.sztaki.hu/~meszaros/public_ftp/lptestset/
    find . -name "index.html*" -delete
    mv old.sztaki.hu/~meszaros/public_ftp/lptestset/* .
    rm -rf old.sztaki.hu
fi

# Compile the emps program
if [ ! -f "emps" ]; then
    gcc -o emps emps.c
fi

# Unzip the files and convert them to SMT-LIB2 format
for file in $(find . -name "*.gz"); do
    filename="${file%.*}"
    gzip -dkf $file -c > $filename.mps.compressed
    rm $file
done

for file in $(find . -name "*.mps.compressed"); do
    if [ $(wc -c < "$file") -ge $max_size ]; then
        echo "Skipping $file because it is too large"
        continue
    fi
    mps_file="${file%.*}"
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

popd > /dev/null || exit

pushd "$script_path" > /dev/null || exit

for file in $(find "$script_path/lp" -name "*.smt2"); do
    mv "$file" "$script_path/smt2"
done

popd > /dev/null || exit

exit 0

