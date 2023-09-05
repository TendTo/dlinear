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

## Enabling autocompletion for `dlinear` and `pydlinear` in bash

### On Ubuntu

```bash
# Install bash-completion
sudo apt install bash-completion
# Move the completion script to the bash-completion directory
sudo cp script/dlinear_completion.sh /etc/bash_completion.d/dlinear.sh
```

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

### Running dlinear from Python

If the package has been installed, either locally or from PyPI, it can be invoked with the same command as the binary.

```shell
pydlinear --help
```

Furthermore, the `pydlinear` module can be imported and used as a library.

```python
import sys
import pydlinear as pdl


def main():
    config = pdl.Config()
    config.filename = "my_file.smt2"
    config.lp_solver = pdl.LPSolver.SOPLEX

    pdl.init_solver(config)
    pdl.Smt2Driver(config).parse_file()


if __name__ == "__main__":
    main()
```
