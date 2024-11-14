# <img alt="Icon" src="docs/_static/logo.svg" align="left" width="35" height="35"> Dlinear

[![dlinear CI](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml/badge.svg)](https://github.com/TendTo/dlinear/actions/workflows/dlinear.yml)
[![Docker CI](https://github.com/TendTo/dlinear/actions/workflows/docker.yml/badge.svg)](https://github.com/TendTo/dlinear/pkgs/container/dlinear)
[![Docs CI](https://github.com/TendTo/dlinear/actions/workflows/docs.yml/badge.svg)](https://tendto.github.io/dlinear/)
[![pydlinear CI](https://github.com/TendTo/dlinear/actions/workflows/pydlinear.yml/badge.svg)](https://pypi.org/project/pydlinear)

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
# Run dlinear
docker run -it --rm ghcr.io/tendto/dlinear:main --help
```

```bash
# ppa repository (Ubuntu)
sudo add-apt-repository ppa:tendto/dlinear
sudo apt update
# Run dlinear
dlinear --help
```

```bash
# pydlinear
pip3 install pydlinear
# Run dlinear
pydlinear --help
```

For more information about the setup, including installation from sources, refer to the [installation guide](docs/Installation.md) and [usage guide](docs/Usage.md).
