# Dlinear

[![dlinear CI](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml)
[![Docker CI](https://github.com/TendTo/dlinear/actions/workflows/docker.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/docker.yml)
[![Docs CI](https://github.com/TendTo/dlinear/actions/workflows/docs.yml/badge.svg)](https://tendto.github.io/dlinear/)

Delta-complete SMT solver for linear programming.
Fork of [dlinear4](https://github.com/martinjos/dlinear4) and [dReal4](https://github.com/dreal/dreal4).

### Installation

The following instructions are for Linux systems.
The installation process for Windows and MacOS is not yet supported.
For more information, refer to the [installation guide](docs/Installation.md).

```bash
bazel build //:package_deb
sudo dpkg -i bazel-bin/dlinear/dlinear.deb
```

### Usage

For more information, refer to the [usage guide](docs/Usage.md).

```bash
dlinear --help
```

### Useful commands

```bash
# Compile dlinear
bazel build //dlinear
# Run dlinear
./bazel-bin/dlinear/dlinear
```

```bash
# CPPlint
bazel test //dlinear/...
```

```bash
# Run dlinear unit tests
bazel test --test_tag_filters=dlinear //test/...
```

```bash
# Run dlinear integration tests by solving a bunch of problems
# and confronting the results with the expected ones
bazel test --test_tag_filters=solver //test/...
```

```bash
# Run linting
bazel test --test_tag_filters=cpplint //dlinear/...
```

### Enabling autocompletion on Ubuntu

```bash
# Install bash-completion
sudo apt install bash-completion
# Move the completion script to the bash-completion directory
sudo cp script/dlinear_completion.sh /etc/bash_completion.d/dlinear.sh
```
