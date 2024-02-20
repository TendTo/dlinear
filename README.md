# Dlinear

[![dlinear CI](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml)
[![Docker CI](https://github.com/TendTo/dlinear/actions/workflows/docker.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/docker.yml)
[![Docs CI](https://github.com/TendTo/dlinear/actions/workflows/docs.yml/badge.svg)](https://tendto.github.io/dlinear/)

Delta-complete SMT solver for linear programming.
Fork of [dlinear4](https://github.com/martinjos/dlinear4) and [dReal4](https://github.com/dreal/dreal4).

## Installation

The following instructions are for Linux systems. The installation process for Windows and MacOS is not yet supported.
For more information, refer to the [installation guide](https://tendto.github.io/dlinear/md_docs_Installation).

```bash
bazel build //:package_deb
sudo dpkg -i bazel-bin/dlinear/dlinear.deb
```

## Usage

For more information, refer to the [usage guide](https://tendto.github.io/dlinear/md_docs_Usage).

```bash
dlinear --help
```

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

## Enabling autocompletion

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

```bash
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
