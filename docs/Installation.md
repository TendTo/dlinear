# Installation

The following instructions are for Linux systems.
The installation process for Windows and MacOS is not yet supported.

## From source

Tested toolchains:

- g++ (Ubuntu 11.4.0-1ubuntu1~22.04) 11.4.0

### Requirements

- [Bazel](https://bazel.build/)
    - The version used for development is 7.3.2. It is suggested to
      use [bazelisk](https://github.com/bazelbuild/bazelisk) to manage Bazel's version.
- [gcc](https://gcc.gnu.org/) for the standard c++ toolchain
- [autoreconf](https://www.gnu.org/software/autoconf/autoconf.html) to compile [qsopt_ex](https://gmplib.org/)
  and [mpfr](https://www.mpfr.org/)
- [libtool](https://www.gnu.org/software/libtool/) to compile [qsopt_ex](https://gmplib.org/)
  and [mpfr](https://www.mpfr.org/)

On a debian based system, the following commands will install all the required dependencies:

```bash
# Install bazelisk (will take care of bazel)
sudo curl -fSsL -o /usr/local/bin/bazel https://github.com/bazelbuild/bazelisk/releases/download/v1.22.0/bazelisk-linux-amd64 
sudo chmod 0755 /usr/local/bin/bazel
# Install the required dependencies
sudo apt install git python3 build-essential automake libtool
```

### Compilation

```bash
# Clone the repository
git clone https://github.com/TendTo/dlinear.git
cd dlinear
# Compile dlinear
bazel build //dlinear
```

The binary will be located in the `bazel-bin/dlinear` directory.

### System wide installation

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
sudo add-apt-repository ppa:tendto/dlinear
# Update the package list
sudo apt update
# Install dlinear
sudo apt install dlinear
```

Most of the dependencies will be installed automatically by the package manager, although the versions may mismatch.
Make sure they match with the ones in the [Module.bazel](../Module.bazel) file.

The shared library expects to find a shared library for each of the dependencies in the system's library path.
If any of those is missing, but a versioned library is present, it is sufficient to create a symbolic link to the
versioned library.

```bash
# Example for libmpfr
sudo ln -s /usr/lib/x86_64-linux-gnu/libmpfr.so.6 /usr/lib/x86_64-linux-gnu/libmpfr.so
```

## From Docker

A pre-build Docker image is available on
the [GitHub repository](https://github.com/TendTo/dlinear/pkgs/container/dlinear).
To use it, run the following command:

```bash
# Pull the image
docker pull ghcr.io/tendto/dlinear:main
# Run the image
docker run -it ghcr.io/tendto/dlinear:main --in --format smt2
```

Notice that this will run the software in interactive mode, meaning it will wait for user input.
To run the binary over a file, mount the file into the container and pass it as an argument to the binary.

```bash
# Run the image with a file
docker run -it -v /path/to/file:/file ghcr.io/tendto/dlinear:main /file
```
