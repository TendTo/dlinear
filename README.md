# Dlinear

Delta-complete SMT solver for linear programming.
Fork of [dlinear4](https://github.com/martinjos/dlinear4) and [dReal4](https://github.com/dreal/dreal4).

## Tested toolchain

- gcc (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0

## Requirements

- [g++](https://gcc.gnu.org/) and [build-essential](https://packages.ubuntu.com/bionic/build-essential)
- [Bazel](https://bazel.build/)
- [gmp](https://gmplib.org/) to compile [qsopt_ex](https://gmplib.org/) and [soplex](https://soplex.zib.de/)
- [autoreconf](https://www.gnu.org/software/autoconf/autoconf.html) to compile [qsopt_ex](https://gmplib.org/)
- [flex](https://github.com/westes/flex) and [bison](https://www.gnu.org/software/bison/) to produce the parser for `.smt2` files

### Useful commands

```bash
# Compile dlinear
bazel build //dlinear
# Run dlinear
bazel-bin/dlinear/dlinear
```

```bash
# CPPlint
bazel test //dlinear/...
```

```bash
# Run tests
bazel test //test/...
```

```bash
# Run benchmarks
bazel run //benchmark
```

### Compilation flags

- `--//tools:enable_dynamic_build=[True|False]` to enable or disable dynamic linking. Used for the python bindings. Default is `False`

## Install Python bindings

### Requirements

- [python-dev](https://packages.ubuntu.com/bionic/python-dev)

### Install

```bash
pip install .
# For development
pip install -e .
```

### Upload to PyPI

```bash
script/upload_pydlinear.sh
```
