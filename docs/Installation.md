# Installation

The following instructions are for Linux systems. The installation process for Windows and MacOS is not yet supported.

## From source

Tested toolchains:

- g++ (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0

### Requirements

- [Bazel](https://bazel.build/)
  - The version used for development is 7.1.1. It is suggested to
    use [bazelisk](https://github.com/bazelbuild/bazelisk) to manage Bazel's version.
- [gcc](https://gcc.gnu.org/) for the standard c++ toolchain
- [autoreconf](https://www.gnu.org/software/autoconf/autoconf.html) to compile [qsopt_ex](https://gmplib.org/)
  and [mpfr](https://www.mpfr.org/)
- [libtool](https://www.gnu.org/software/libtool/) to compile [qsopt_ex](https://gmplib.org/)
  and [mpfr](https://www.mpfr.org/)

#### apt

```bash
sudo apt install g++ libtool
```

#### pacman

```bash
sudo pacman -S gcc libtool
```

#### Optional requirements

- [patchelf](https://github.com/NixOS/patchelf) allows to create a fully self-contained shared library. Enabled
  by `--//tools:enable_patchelf=True` during compilation

### Compilation

```bash
# Clone the repository
git clone https://github.com/TendTo/dlinear.git
cd dlinear
# Compile dlinear
bazel build //dlinear
```

The binary will be located in the `bazel-bin/dlinear` directory.

### Installation (Debian based systems)

```bash
# Install dlinear
bazel build //:package_deb
sudo dpkg -i bazel-bin/dlinear/dlinear.deb
```

## Packaging

dlinear includes a packaging system to create a distributable package for the most common Linux distributions.

### Debian

#### Requirements

- [gmp 6.3.0](https://gmplib.org/)
- [mpfr 4.2.1](https://www.mpfr.org/)
- [fmt 10.2.1](https://fmt.dev/)
- [spdlog 1.12.0](https://github.com/gabime/spdlog)
- [soplex](https://soplex.zib.de/)

Most of the dependencies can be installed using the package manager of the system, although the versions may mismatch.

```bash
sudo apt install libgmp-dev libmpfr-dev libfmt-dev libspdlog-dev
```

The soplex library must be compiled from source.
Follow the instructions [installation file](https://github.com/scipopt/soplex/blob/master/INSTALL.md).

The shared library expects to find a shared library for each of the dependencies in the system's library path, as `libgmp.so`, `libmpfr.so`, `libfmt.so`, and `libspdlog.so`.
If any of those is missing, but a versioned library is present, it is sufficient to create a symbolic link to the versioned library.

```bash
# Example for libmpfr
sudo ln -s /usr/lib/x86_64-linux-gnu/libmpfr.so.6 /usr/lib/x86_64-linux-gnu/libmpfr.so
```

#### Linking against the shared library

When including the shared library in a project, make sure to define the following macros, either before including the header or in the compilation command.

```cpp
#define SPDLOG_FMT_EXTERNAL
#define SPDLOG_COMPILED_LIB

#include <dlinear/dlinear.h>
```

or in the compilation command

```bash
g++ -std=c++20 -Iinclude <my_file>.cpp -lgmp lib/libdlinear.so -o a.out -DSPDLOG_FMT_EXTERNAL -DSPDLOG_COMPILED_LIB
```

When running the binary, make sure to include the path to the shared libraries, especially if they are not in the system's library path, like soplex.

```bash
LD_LIBRARY_PATH=/usr/local/lib ./a.out
```
