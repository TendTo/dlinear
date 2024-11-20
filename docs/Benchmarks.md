# Benchmarks

dlinear has been tested on a variety of QF_LRA SMT benchmarks, including the [SMT-LIB QF_LRA 2023 benchmarks](https://doi.org/10.5281/zenodo.10607722) and various LP problems, such as [the MIPLIB benchmarking suite](https://miplib.zib.de/tag_benchmark.html), the [Netlib LP tests](http://www.netlib.org/lp/data/) and the [Csaba Mészáros' LP collection](http://old.sztaki.hu/~meszaros/public_ftp/lptestset/).
The `benchmark` folder contains some utility script that have been used to collect and analyse the results.

## Artifacts

### TACAS 2025

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.14161448.svg)](https://doi.org/10.5281/zenodo.14161448)

- Tool version: `0.0.1`

This is the artifact produced by version 0.0.1 of the tool. It contains the executable tool we used to produce the results shown in the benchmarks section of the paper, along with a set of "csv" files with the data we collected and the over 3000 input files, which are also publicly available online (e.g. SMT-LIB QF-LRA benchmarks).
The "benchmarks.sh" script handles the setup automatically, as well as providing some utilities when running the benchmarks.
The tool can be used both as a standalone binary and as a library, as shown in the main.cpp example file.

> [!NOTE]  
> This artifact is meant to run on the TACAS 2023 Artifact Evaluation Virtual Machine and may not work on other systems.
> Check the REAMDE.md, the main repository or the documentation for alternative methods of installation.
