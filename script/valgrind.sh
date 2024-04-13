#!/bin/bash

# Run dlinear with Valgrind in order to detect memory leaks.
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
readonly root_dir="$script_path/.."

valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes --verbose --log-file=valgrind-out.txt "$root_dir/bazel-bin/dlinear/dlinear" $@
# valgrind --tool=drd --tool=massif --log-file=valgrind-memory-out.txt "$root_dir/bazel-bin/dlinear/dlinear" $@
