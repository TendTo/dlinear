# Usage

After [compilation](./Installation.md), the `dlinear` binary will be located in the `bazel-bin/dlinear` directory.
There are several options to run it:

- run `./bazel-bin/dlinear/dlinear` in the terminal
- add the absolute path of the directory `bazel-bin/dlinear` to the `PATH` environment variable
- move the binary from `./bazel-bin/dlinear/dlinear` to a directory already in the `PATH`, like `/usr/local/bin`
- create a symbolic link to the executable
- create an alias for the executable

From now on, the snippets will assume that the `dlinear` binary has been added to the `PATH`.

```bash
# Invoke dlinear help
dlinear -h
```

## File mode

By default, _dlinear_ expects the path to the problem file as the only positional argument.
The file can be in the [SMT2](https://smtlib.cs.uiowa.edu/language.shtml) or [MPS](<https://en.wikipedia.org/wiki/MPS_(format)>) format.
If left unspecified, the program will look at the file extension to determine the format.

```bash
# Invoke dlinear with a problem in SMT2 format
dlinear path/to/problem.smt2
# Invoke dlinear with a problem in MPS format
dlinear path/to/problem.mps
# Invoke dlinear with a problem assuming it is in SMT2 format
dlinear path/to/problem --format smt2
```

## Stdin mode

_dlinear_ can be used in stdin mode, where the user can input is received from the standard input.
Note that in this case the format must be specified explicitly.

```bash
# Invoke dlinear in stdin mode (SMT2 format)
dlinear --in --format smt2
# Invoke dlinear in stdin mode (MPS format)
dlinear --in --format mps
```

When the stdin mode is used, the problem must be typed directly in the terminal.
To signal dlinear the end of the input, press `Ctrl+D` two times.
This will start the solver.

## Neural network verification

_dlinear_ can be used to verify the robustness of a neural network.
The network must be in the [ONNX](https://onnx.ai/) format, while the property must be in the [VNN-LIB](https://www.vnnlib.org/) format.
To run the verification, use the following command:

```bash
# Invoke dlinear with a neural network and a property
dlinear --onnx path/to/network.onnx path/to/property.vnnlib
```
