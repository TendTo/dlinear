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
