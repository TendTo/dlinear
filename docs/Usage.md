# Use

After compilation, the binary, called `dlinear` will be located in the `bazel-bin/dlinear` directory.
To run it, just type `bazel-bin/dlinear/dlinear` in the terminal.

```bash
# Invoke dlinear help
bazel-bin/dlinear/dlinear -h
```

## File mode

By default, _dlinear_ expects the path to the problem file as the only positional argument.
The file can be in the [SMT2](https://smtlib.cs.uiowa.edu/language.shtml) or [MPS](<https://en.wikipedia.org/wiki/MPS_(format)>) format.
If left unspecified, the program will look at the file extension to determine the format.

```bash
# Invoke dlinear with a problem in SMT2 format. --format smt is not necessary
bazel-bin/dlinear/dlinear path/to/problem.smt2
# Invoke dlinear with a problem in MPS format. --format mps is not necessary
bazel-bin/dlinear/dlinear path/to/problem.mps
```

## Stdin mode

_dlinear_ can be used in stdin mode, where the user can input is received from the standard input.
By default, the program will expect a problem in the [SMT2](https://smtlib.cs.uiowa.edu/language.shtml) format.

```bash
# Invoke dlinear in stdin mode (SMT2 format)
bazel-bin/dlinear/dlinear --in
# Invoke dlinear in stdin mode (MPS format)
bazel-bin/dlinear/dlinear --in --format mps
```

When the stdin mode is used, the problem can be typed directly in the terminal.
When it is complete, press `Ctrl+D` two times to signal the end of the input.
