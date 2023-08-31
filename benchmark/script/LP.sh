#!/bin/bash
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
readonly max_size=100000000

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

# Decompress the files using the emps program
for file in $(find . -name "*.mps.compressed"); do
    if [ $(wc -c < "$file") -ge $max_size ]; then
        echo "Skipping $file because it is too large"
        continue
    fi
    mps_file="${file%.*}"
    ./emps -1 -b -m $file > $mps_file
    rm $file
done

# Convert from MPS to SMT-LIB2 format
for file in $(find . -name "*.mps"); do
    smt2_file=LP_$(basename "$file" .mps).smt2
    echo "Converting $file to SMT-LIB2 format..."
    ../mps2smt2-py/mps2smt2.py -c "$file" > "$smt2_file" # could also add --max --delta for an objective function
    rm $file
done

popd > /dev/null || exit

pushd "$script_path" > /dev/null || exit

for file in $(find "$script_path/lp" -name "*.smt2"); do
    mv "$file" "$script_path/smt2"
done

popd > /dev/null || exit

exit 0
