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

### Compilation

```bash
# Clone the repository
git clone https://github.com/TendTo/dlinear.git
cd dlinear
# Compile dlinear
bazel build //dlinear
```

The binary will be located in the `bazel-bin/dlinear` directory.

### System wide installation (Debian based systems)

To install the binary along with the shared library and the header files system wide, run the following command:

```bash
# Install dlinear
bazel build //package:debian
sudo dpkg -i bazel-bin/dlinear/dlinear.deb
```

## From package manager

### Debian based systems (Debian, Ubuntu, etc.)

`dlinear` is also distributed as a Debian package through a Personal Package Archive (PPA) hosted on Launchpad.

```bash
# Add the PPA
sudo add-apt-repository ppa:dlinear/dlinear
# Update the package list
sudo apt update
# Install dlinear
sudo apt install dlinear
```

#### Requirements

- [soplex](https://soplex.zib.de/)

Most of the dependencies will be installed automatically by the package manager, although the versions may mismatch.
Make sure they match with the ones in the [Module.bazel](../Module.bazel) file.

The soplex library, unfortunately, must be compiled from source.
Follow the instructions [installation file](https://github.com/scipopt/soplex/blob/master/INSTALL.md).

The shared library expects to find a shared library for each of the dependencies in the system's library path.
If any of those is missing, but a versioned library is present, it is sufficient to create a symbolic link to the versioned library.

```bash
# Example for libmpfr
sudo ln -s /usr/lib/x86_64-linux-gnu/libmpfr.so.6 /usr/lib/x86_64-linux-gnu/libmpfr.so
```
