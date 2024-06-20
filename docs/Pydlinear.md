# Pydlinear

`pydlinear` is a Python package that provides bindings to the `dlinear` library.
The package can be used to create and solve linear programs from Python.

## From source

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

## From PyPI

```bash
pip install pydlinear
```

## Usage

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
