# Pydlinear

`pydlinear` is a Python package that provides bindings to the `dlinear` library.
The package can be used to create and solve linear programs from Python.

## From source

Clone the repository and install the package with pip.

### Requirements

- [python-dev](https://packages.ubuntu.com/bionic/python-dev)

### Install

```bash
pip install .
# For development
pip install -e .
```

## From PyPI

```bash
pip install pydlinear
```

## Usage

If the package has been installed, either locally or from PyPI, it can be invoked with the same options as the binary.

```bash
pydlinear --help
```

Furthermore, the `pydlinear` module can be imported and used as a library.

```python
import sys
import pydlinear as pdl


config = pdl.Config.from_args(sys.argv)
solver = pdl.SmtSolver(config)
solver.Parse()
result = solver.CheckSat()
sys.exit(result.exit_code)
```
