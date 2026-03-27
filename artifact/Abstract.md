# Abstract

This artifact accompanies the tool paper **dLinear: Enhancing SMT Solvers with Floating-Point Exact LP Solvers** and is intended to reproduce the experimental results reported in the paper’s *Benchmarks* section.

The paper evaluates the performance of **dLinear** (a modified version of **cvc5**) on standard SMT-LIB benchmarks for **QF_LRA** (SMT-LIB 2025 suite), and compares it against the baselines **cvc5 1.3.2**, **cvc5+GLPK** (as in the prior cvc5 LP integration), and the state-of-the-art SMT solvers **Z3 4.13.0** and **Yices 2.7.0**. The benchmark runs use a timeout of **6 hours** per instance, with **1 core** and **4 GB RAM**.

In the paper, results are reported on the subset of SMT-LIB instances where the solver configuration triggers at least one call to an external LP solver after a bounded number of internal simplex/tableau pivots. 
Concretely, the evaluated pivot thresholds are **n = 100** and **n = 200**, yielding subsets of **319** and **177** instances, respectively. 
For dLinear, the evaluated configurations cover:

- the external exact LP backend (**SoPlex** or **QSopt_ex**),
- the handling of strict inequalities (either via a conservative **$\varepsilon$-perturbation** or by introducing a strictness variable **$t$**), and
- the pivot threshold **n** before switching to the external LP solver.

The submitted artifact contains a **self-contained Docker image** that includes the **dLinear binary** and the scripts needed to rerun these experiments.
The docker image also contains the **csv file** with all the reported results, plus a notebook to generate the plots and tables presented in the paper.

**Reproducible experiments:** all benchmark experiments and derived plots/tables reported in the paper’s *Benchmarks* section for the complete configurations.

**Paper type:** Tool paper.
