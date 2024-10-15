# Dlinear

[![dlinear CI](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml)
[![Docker CI](https://github.com/TendTo/dlinear/actions/workflows/docker.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/docker.yml)
[![Docs CI](https://github.com/TendTo/dlinear/actions/workflows/docs.yml/badge.svg)](https://tendto.github.io/dlinear/)
[![pydlinear CI](https://github.com/TendTo/dlinear/actions/workflows/pydlinear.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/pydlinear.yml)

Delta-complete SMT solver for linear theories over the reals.
Fork of [dlinear4](https://github.com/martinjos/dlinear4) and [dReal4](https://github.com/dreal/dreal4).

### Installation

There are multiple ways of installing dlinear.
The recommanded approach is to use the official [Docker image](https://github.com/TendTo/dlinear/pkgs/container/dlinear), the [ppa repository](https://launchpad.net/~tendto/+archive/ubuntu/dlinear) or the python wrapper [_pydlinear_](https://pypi.org/project/pydlinear).

> [!Note]
> Only Linux is supported, but using the Docker image circumvents this limitation.

```bash
# Docker
docker pull ghcr.io/tendto/dlinear:main
docker run -it --rm ghcr.io/tendto/dlinear:main --help
```

```bash
# ppa repository
sudo add-apt-repository ppa:tendto/dlinear
sudo apt update
```

```bash
# pydlinear
pip3 install pydlinear
pydlinear --help
```

For more information about the installation process options, including installation from sources, refer to the [installation guide](docs/Installation.md).

### Usage

For more information, refer to the [usage guide](docs/Usage.md).

```bash
dlinear --help
# Use `pydlinear --help` if you installed the pydlinear wrapper
```
