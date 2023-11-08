# Dlinear

[![dlinear CI](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml)

Delta-complete SMT solver for linear programming.
Fork of [dlinear4](https://github.com/martinjos/dlinear4) and [dReal4](https://github.com/dreal/dreal4).

## Tested toolchain

- gcc (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0

## Requirements

- [g++](https://gcc.gnu.org/) and [build-essential](https://packages.ubuntu.com/bionic/build-essential)
- [Bazel](https://bazel.build/)
- [gmp](https://gmplib.org/) to compile [qsopt_ex](https://gmplib.org/) and [soplex](https://soplex.zib.de/)
- [autoreconf](https://www.gnu.org/software/autoconf/autoconf.html) to compile [qsopt_ex](https://gmplib.org/)
- [libtool](https://www.gnu.org/software/libtool/) to compile [qsopt_ex](https://gmplib.org/)
- [flex](https://github.com/westes/flex) and [bison](https://www.gnu.org/software/bison/) to produce the parser for `.smt2` and `.mps` files

## Default parsing and solving behavior

dlinear will parse and solve problems in `smt2` or `mps` format.
The default behavior is to parse the input and produce a satisfiability result, either `delta-sat` or `unsat`.

> **Warning**  
> Some `smt` directives will be ignored, since their role is taken by the command line flags:
>
> - `(check-sat)` is assumed to be present by default. It can be disabled with `--no-check-sat`
> - `(produce-models)` is ignored by default. It can be enabled with `-m/--produce-models`
> - `(minimize)`/`(maximize)` are ignored by default. They can be enabled with `-m/--produce-models`
>
>   This also implies that, when parsing a `mps` file, the objective function is ignored, unless the `-m/--produce-models` flag is used.

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
# Run dlinear unit tests
bazel test --test_tag_filters=dlinear //test/...
```

```bash
# Run dlinear integration tests by solving a bunch of problems
# and confronting the results with the expected ones
bazel test --test_tag_filters=solver //test/...
```

```bash
# Run linting
bazel test --test_tag_filters=cpplint //dlinear/...
```

```bash
# Run pydlinear tests
bazel test --test_tag_filters=pydlinear //pydlinear/...
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
    config = pdl.Config.from_command_line(sys.argv)
    with pdl.Solver(config) as s:
        print(s.CheckSat())


if __name__ == "__main__":
    main()

```
