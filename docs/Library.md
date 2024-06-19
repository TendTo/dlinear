# Library

`dlinear` comes with a shared C++ library that can be used to interact with the solver programmatically.

## From source

To build the library from source, run the following command:

```bash
bazel build --enable_fpic_build //dlinear:libdlinear.so
```

The library will be located in the `bazel-bin/dlinear/libdlinear.so` directory.

## Requirements

To use the library, you will need the following dependencies installed on your system:

- [gmp](https://gmplib.org/)
- [zlib](https://zlib.net/)
- [soplex](https://soplex.zib.de/)
- [spdlog (headers)](https://github.com/gabime/spdlog)
- [fmt (headers)](https://github.com/fmtlib/fmt)

Check that the version of the dependencies match the one indicated in the [Module.bazel](../Module.bazel) file.

## Using the library

To be able to use the library, you will need the shared library as well as the header files.
To obtain both, run the following command:

```bash
bazel build //package:package
```

This will create a tarball in the `bazel-bin/package` directory that contains the shared library and the header files.
You can then extract the tarball to a directory of your choice and use the library from there.

```bash
tar -xvf bazel-bin/package/package.tar.gz -C . # Extract the tarball to the current directory
```

Three folders will be extracted: `include`, `lib`, and `bin`.
The `include` folder contains the header files, the `lib` folder contains the shared library, and the `bin` folder contains the binary executable.

### Linking

When including the shared library in a project, make sure to define the following macros, before including the dlinear header

```cpp
#define SPDLOG_FMT_EXTERNAL
#define SPDLOG_COMPILED_LIB

#include <dlinear/dlinear.h>
```

or, even better, in the compilation command

```bash
g++ -std=c++20 <my_file>.cpp -lgmp -ldlinear -o a.out -DSPDLOG_FMT_EXTERNAL -DSPDLOG_COMPILED_LIB
```

## Example

The following example demonstrates how to use the library to check the satisfiability of a problem in SMT2 format:

```cpp
/**
 * @file test.cpp
 */
// Needed to indicate that an external fmt library version is in use
#define SPDLOG_FMT_EXTERNAL
// Needed to indicate that the spdlog library is compiled inside the shared library
#define SPDLOG_COMPILED_LIB

#include <dlinear/solver/SmtSolver.h>

#include <iostream>

int main() {
  dlinear::Config config;
  dlinear::SmtSolver solver;
  solver.Parse("input.smt2");
}
```

The example can be compiled with

```bash
g++ -std=c++20 test.cpp -lgmp -ldlinear -o test
```

and run with

```bash
./test
```
