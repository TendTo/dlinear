#!/bin/bash

# Run dlinear with Valgrind in order to detect memory leaks.
readonly script_path="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 || exit ; pwd -P )"
readonly root_dir="$script_path/.."

sudo sysctl -w kernel.perf_event_paranoid=0

perf record -g "$root_dir/bazel-bin/dlinear/dlinear" $@
