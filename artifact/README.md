# dlinear Artifact (Docker-based)

This folder contains the **required artifact materials** for an AE review:

- this **README** with step-by-step instructions,
- the [**LICENCE**](./LICENCE) file, and
- a **Docker image archive** (produced via `docker save` and shipped as `qest-formats-ae-image.tar.gz`) containing all binaries and benchmarks needed to run the experiments **without network access**.

The Docker image archive is meant to be shipped as part of the final `artifact.tar.gz` submission.

## Requirements

To run the experiments, reviewers will need:

- Docker (tested with Docker version 29.3.0)
- ~10 GB free disk space for the image + results (depends on compression)

## Configurations

By default, all experiments (i.e., each benchmark instance) will be run with the following configurations:

- **cvc5 baseline**: cvc5 with the default configuration, without any cuts or LP solver.
- **cvc5+glpk**: cvc5 with the glpk cut generator, with 100, 200, and 300 iterations.
- **cvc5+soplex**: cvc5 with the soplex cut generator, with 100, 200, and 300 iterations, and modes: default, strict, and delta.
- **cvc5+qsoptex**: cvc5 with the qsoptex cut generator, with 100, 200, and 300 iterations, and modes: default, strict, and delta.

## Experiments

### Smoke test

The smoke test is a quick sanity check that runs a single benchmark instance with all configurations, to verify that the image is functional and the expected outputs are produced.

```bash
bash ./run.sh
```

#### Expected outputs

On the first run, the script will load the Docker image from `qest-formats-ae-image.tar.gz` (if it is not already present locally). It will then launch a container and solve one benchmark with all configurations.

The output will look similar to:

```
[artifact] Running smoke test
[artifact] Using benchmark listed in /instances/smoke.csv
[artifact] Running smoke test
...
[artifact] Running cvc5 baseline
[artifact] Running cvc5
Local mode: running first 1 benchmarks
Reading file /benchmarks/constraints-tms-2-3-light-40.smt2
Read 1 lines
Storing 1 lines, failed to parse 0 lines
[artifact] Running glpk
[artifact] Running glpk with 100 iterations
Local mode: running first 1 benchmarks
Reading file /benchmarks/constraints-tms-2-3-light-40.smt2
Read 1 lines
Storing 1 lines, failed to parse 0 lines
...
Read 1 lines
Storing 1 lines, failed to parse 0 lines
[artifact] Running qsoptex with 300 iterations and mode delta
Local mode: running first 1 benchmarks
Reading file /benchmarks/constraints-tms-2-3-light-40.smt2
Read 1 lines
Storing 1 lines, failed to parse 0 lines
[artifact] Smoke test complete.
```

After the run completes, the script launches JupyterLab (inside a container) to visualize the results.

To access the GUI in your browser, look for a line like:

```
[I 2026-03-26 18:00:41.239 ServerApp] Jupyter Server 2.17.0 is running at:
[I 2026-03-26 18:00:41.239 ServerApp] http://localhost:8888/lab?token=51d44fc4f44ec4fba11187448c5bb6fffc410a4b476329ee
[I 2026-03-26 18:00:41.239 ServerApp]     http://127.0.0.1:8888/lab?token=51d44fc4f44ec4fba11187448c5bb6fffc410a4b476329ee
[I 2026-03-26 18:00:41.239 ServerApp] Use Control-C to stop this server and shut down all kernels (twice to skip confirmation).
[C 2026-03-26 18:00:41.241 ServerApp]

    To access the server, open this file in a browser:
        file:///home/jovyan/.local/share/jupyter/runtime/jpserver-7-open.html
    Or copy and paste one of these URLs:
        http://localhost:8888/lab?token=51d44fc4f44ec4fba11187448c5bb6fffc410a4b476329ee
        http://127.0.0.1:8888/lab?token=51d44fc4f44ec4fba11187448c5bb6fffc410a4b476329ee
```

Click (or copy-paste) the URL to open the JupyterLab interface in your browser, where you can explore the results of the smoke test.
Select the `results.ipynb` notebook, and click on `Run > Run All Cells` to execute the notebook and visualize the results.

### Running the tool

By default, `run.sh` runs the smoke test (suite name `smoke`). You can run a different benchmark suite by passing the suite name and an optional per-configuration limit:

- The suite name corresponds to a CSV file in `instances/` (without the `.csv` extension).
- The CSV is read from `/instances/<suite>.csv` volume inside the container.
- By default, the script runs the first 6 instances per configuration.

Results are written to `results-<suite>/` in this folder, and JupyterLab is launched afterward (same as the smoke test).

```bash
bash ./run.sh [benchmark suite name, default: smoke] [limit of instances to run per configuration, default: 6]
# E.g.,
bash ./run.sh lanteresse 3
```

You are free to modify any of the CSV files in `instances/` to run different sets of benchmarks.
We recommend editing `instances/custom.csv` to keep the original files intact.

The first line is treated as a header and skipped; each subsequent row should provide a file name relative to the SMT-LIB benchmark directory in the image.
Keep in mind that only [QF_LRA](https://smt-lib.org/logics-all.shtml#QF_LRA) theory benchmarks from the [SMT-LIB release 2025 of non-incremental benchmarks](https://zenodo.org/records/16740866) are available.

```csv
file
my_benchmark_1_from_smtlib.smt2
my_benchmark_2_from_smtlib.smt2
```

```bash
bash ./run.sh custom 2
```

### Exploring the results from the paper

All results from the **Benchmark** section of the paper are included in the artifact as CSV files (see `results/`).
A Jupyter notebook is provided to explore these results and regenerate the tables and plots.

```bash
bash ./explore.sh
```
