#!/bin/bash
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
readonly root_path="$script_path/.."
readonly eg_sloan_path="$root_path/submodules/qsopt-ex/build/tests"

function parse_args() {
    local param=""
    a="3"
    b="3"
    c="3"
    e="3"
    t="2"
    while [ $# -gt 0 ]; do
        param="$1"
        shift
        case "$param" in
            -h | --help )
                echo "Usage: $0 [OPTION]"
                echo "The output file is written to $script_path/smt2 as a .smt2 file."
                echo "The name of the output file will be the combination of the arguments: {a}-{b}-{c}-{e}-{t}.smt2}"
                echo "Options:"
                echo "  -h, --help      Display this help message"
                echo "  -a              Range of values for the first OA level (>= 2)"
                echo "  -b              Range of values for the second OA level (>= 2)"
                echo "  -c              Number of columns for the first OA level (>= 2)"
                echo "  -e              Number of columns for the second OA level (>= 2)"
                echo "  -t              Strength of the OA"
                exit 0
            ;;
            -a )
                if [ -z "$1" ]; then
                    echo "Missing argument for $param"
                    exit 1
                fi
                a="$1"
                shift
            ;;
            -b )
                if [ -z "$1" ]; then
                    echo "Missing argument for $param"
                    exit 1
                fi
                b="$1"
                shift
            ;;
            -c )
                if [ -z "$1" ]; then
                    echo "Missing argument for $param"
                    exit 1
                fi
                c="$1"
                shift
            ;;
            -e )
                if [ -z "$1" ]; then
                    echo "Missing argument for $param"
                    exit 1
                fi
                e="$1"
                shift
            ;;
            -t )
                if [ -z "$1" ]; then
                    echo "Missing argument for $param"
                    exit 1
                fi
                t="$1"
                shift
            ;;
            * )
                echo "Unknown option: $param"
                exit 1
            ;;
        esac
    done
}

parse_args "$@"
echo "Building eg_sloan"
echo "================="

readonly output_file="${a}-${b}-${c}-${e}-${t}"

pushd "$eg_sloan_path" > /dev/null || exit
./eg_sloan -d 1 -m 1 -o "$script_path/smt2/$output_file.mps" -a "$a" -b "$b" -c "$c" -e "$e" -t "$t"
popd > /dev/null || exit
pushd "$script_path/smt2" > /dev/null || exit
echo "Converting to SMT2"
toyconvert "$output_file.mps" -o "$output_file.smt2"
sed -i 's/(set-option :produce-models true)/(set-logic QF_LRA)/' "$output_file.smt2"
sed -i 's/(!//' "$output_file.smt2"
sed -i 's/ *:named[^)]*)//' "$output_file.smt2"
rm "$output_file.mps"
rm -f "toyconvert.tix"
echo "Done"
popd > /dev/null || exit

# toyconvert output.mps -o output.smt2