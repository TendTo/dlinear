# Usage

After compilation, the binary, called `dlinear` will be located in the `bazel-bin/dlinear` directory.
There are several options to run it:

- run `bazel-bin/dlinear/dlinear` in the terminal
- add the absolute path of the directory `bazel-bin/dlinear` to the `PATH` environment variable
- create a symbolic link to the executable
- create an alias for the executable

From now on, the snippets will assume that the `dlinear` binary is in the `PATH`.

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
# Invoke dlinear with a problem enforcing the SMT2 format
dlinear path/to/problem --format smt2
```

## Stdin mode

_dlinear_ can be used in stdin mode, where the user can input is received from the standard input.

```bash
# Invoke dlinear in stdin mode (SMT2 format)
dlinear --in --format smt2
# Invoke dlinear in stdin mode (MPS format)
dlinear --in --format mps
```

When the stdin mode is used, the problem can be typed directly in the terminal.
When it is complete, press `Ctrl+D` two times to signal the end of the input.
