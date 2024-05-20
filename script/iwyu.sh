#!/bim/bash
# apt install clang libstdc++-12-dev
CXX=clang bazel build --config=iwyu --config=debug //dlinear/...

bazel build --config=dwyu //dlinear
