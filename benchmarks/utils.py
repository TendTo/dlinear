import subprocess
import re
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from itertools import combinations
from functools import reduce


GLPK = 1
SOPLEX = 2
QSOPTEX = 3

plt.rcParams.update(
    {
        "text.usetex": True,
        "font.size": 11,
        "axes.titlesize": 12,
        "axes.labelsize": 11,
        "legend.fontsize": 10,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "font.family": "serif",
        "font.serif": ["Times New Roman"]
    }
)

def parse_duration_to_ms(value):
    """
    Convert duration strings like '5707ms', '1.5s', '2m', '1h' to milliseconds.
    Returns the value as float if it's a duration, otherwise returns the original value.
    """
    if not isinstance(value, str):
        return value

    # Match patterns like '123ms', '1.5s', '2m', '1h'
    match = re.match(r"^(\d+\.?\d*)(\w+)$", value)
    if not match:
        return value

    num, unit = match.groups()
    num = int(num)

    # Convert to milliseconds
    unit_conversions = {"ms": 1, "s": 1000, "m": 60000, "h": 3600000}

    if unit in unit_conversions:
        return num * unit_conversions[unit]

    return value


def convert_to_numeric(value: str):
    """
    Convert string values to int or float where appropriate.
    Returns the converted value or the original if conversion isn't appropriate.
    """
    if not isinstance(value, str):
        return value

    # Skip empty strings and special markers
    if value == "" or value.startswith("{"):
        return value

    # Try duration conversion first
    duration_result = parse_duration_to_ms(value)
    if duration_result != value:
        return duration_result

    # Try to convert to int
    try:
        # Check if it looks like an integer (no decimal point)
        if "." not in value:
            return int(value)
    except ValueError:
        pass

    # Try to convert to float
    try:
        return float(value)
    except ValueError:
        pass

    # Return original value if no conversion worked
    return value


def split_dict_columns(value: str, prefix: str) -> pd.Series:
    if not isinstance(value, str) or not value.startswith("{") or not value.endswith("}"):
        return pd.Series()

    # Remove the curly braces and split by comma
    entries = value[1:-1].split(",")
    precision_dict = {}
    for entry in entries:
        if ":" in entry:
            precision, count = f"{prefix}_{entry.split(':')[0].strip()}", int(entry.split(":")[1].strip())
            precision_dict[precision] = count
    return pd.Series(precision_dict)


@dataclass
class SolverResult:
    dataframe: pd.DataFrame
    solver_name: str
    solver_id: str
    iterations: int = -1

    @property
    def result_key(self) -> str:
        return f"result{self.solver_id}"

    def apply_filter(self, filter_func):
        return SolverResult(dataframe=filter_func(self.dataframe), solver_name=self.solver_name, solver_id=self.solver_id, iterations=self.iterations)

    def replace_df(self, new_df: pd.DataFrame):
        return SolverResult(dataframe=new_df, solver_name=self.solver_name, solver_id=self.solver_id, iterations=self.iterations)


def query_time(*results: SolverResult, instances: str | tuple[str]):
    if isinstance(instances, str):
        instances = (instances,)
    time_table = pd.DataFrame(columns=(result.solver_name for result in results))
    for instance in instances:
        values = [result.dataframe.loc[instance][f"time{result.solver_id}"] for result in results]
        time_table.loc[instance] = values
    return time_table


def get_tot_results_compare(ours: SolverResult, other: SolverResult) -> int:
    tot = 1753
    solved = len(other.dataframe[other.dataframe[other.result_key].isin(["sat", "unsat"])])
    not_solved = tot - solved
    outer_merge = pd.merge(
        other.dataframe[other.dataframe[other.result_key].isin(["sat", "unsat"])][[other.result_key]],
        ours.dataframe[ours.dataframe[ours.result_key].isin(["sat", "unsat"])][[ours.result_key]],
        left_index=True,
        right_index=True,
        how="outer",
    )
    other_vetter = len(outer_merge[outer_merge[ours.result_key].isna() & outer_merge[other.result_key].notna()])
    ours_better = len(outer_merge[outer_merge[other.result_key].isna() & outer_merge[ours.result_key].notna()])
    not_matching_results = len(
        outer_merge[
            (outer_merge[other.result_key] != outer_merge[ours.result_key])
            & outer_merge[other.result_key].notna()
            & outer_merge[ours.result_key].notna()
        ]
    )
    in_common = len(outer_merge[outer_merge[other.result_key] == outer_merge[ours.result_key]])
    assert in_common + other_vetter == solved, f"{in_common} + {other_vetter} != {solved}"
    return f"""
#### {other.solver_name} comparison with {ours.solver_name}

| Theory     | Number of instances | Solved instances | Unsolved instances | Not matching results   | In common      | {ours.solver_name} only     | {other.solver_name} only     |
| ---------- | ------------------- | ---------------- | ------------------ | ---------------------- | -------------- | ------------- | -------------- |
| **QF_LRA** | {tot}               | {solved}         | {not_solved}       | {not_matching_results} | {in_common}    | {ours_better} | {other_vetter} |
"""


def copy_instances(df: pd.DataFrame, base_dir: str = "/home/campus.ncl.ac.uk/c3054737/Downloads/QF_LRA"):
    """
    Copy rows from the dataframe that match the instance names in the instance_list.
    """
    cmds = df["file"].apply(lambda x: f"find {base_dir} -name '*{x}' -exec cp {{}} QF_LRA \\;").to_list()
    for cmd in cmds:
        subprocess.run(cmd, shell=True, check=True)


def compare_unique_solved_instances(*solvers: SolverResult) -> tuple[pd.DataFrame, pd.DataFrame]:
    """
    Compare solved instances (sat/unsat) across an arbitrary number of solver dataframes.

    Returns:
        for each solver pair (A, B), counts solved only by A, only by B, and in common.
    """
    if len(solvers) < 2:
        raise ValueError("At least two SolverResult inputs are required")

    solved_values = {"sat", "unsat"}
    solved_sets: dict[str, set] = {}

    for solver in solvers:
        if solver.result_key not in solver.dataframe.columns:
            raise KeyError(f"Column '{solver.result_key}' not found in dataframe for {solver.solver_name}")

        solver_name = solver.solver_name
        solved_sets[solver_name] = set(solver.dataframe.index[solver.dataframe[solver.result_key].isin(solved_values)])

    solver_names = list(solved_sets.keys())

    pairwise_rows = []
    for left, right in combinations(solver_names, 2):
        left_only = len(solved_sets[left] - solved_sets[right])
        right_only = len(solved_sets[right] - solved_sets[left])
        in_common = len(solved_sets[left] & solved_sets[right])
        pairwise_rows.append(
            {
                "solver_a": left,
                "solver_b": right,
                "a_only": left_only,
                "b_only": right_only,
                "in_common": in_common,
            }
        )

    pairwise_only = pd.DataFrame(pairwise_rows)

    return pairwise_only


def build_markdown_comparison_matrix(
    pairwise_only: pd.DataFrame,
    solver_order: list[str],
) -> str:
    """
    Build a markdown report with:
    1) pairwise matrix M[i][j] = solved by i but not by j (diagonal = total solved by i),
    2) exclusive solved counts by solver-combination.
    """
    pairwise_counts: dict[tuple[str, str], int] = {}
    solved_totals = {name: "" for name in solver_order}

    for _, row in pairwise_only.iterrows():
        a = row["solver_a"]
        b = row["solver_b"]
        pairwise_counts[(a, b)] = int(row["a_only"])
        pairwise_counts[(b, a)] = int(row["b_only"])

    header = "| Solver A \\ Solver B | " + " | ".join(solver_order) + " |"
    sep = "| --- | " + " | ".join(["---"] * len(solver_order)) + " |"
    matrix_rows = []

    for a in solver_order:
        row_cells = []
        for b in solver_order:
            value = solved_totals[a] if a == b else pairwise_counts.get((a, b), 0)
            row_cells.append(str(value))
        matrix_rows.append(f"| {a} | " + " | ".join(row_cells) + " |")

    return "\n".join(
        [
            "### Pairwise matrix (instances solved by row solver but not by column solver)",
            header,
            sep,
            *matrix_rows,
        ]
    )


def plot_performance_profiles(
    *results: SolverResult,
    metric_cols: str | list[str] = "time",
    result_cols: str | list[str] = "result",
    accepted_results: tuple[str, ...] = ("sat", "unsat"),
    max_tau: float = None,
    num_points: int = 1000,
    metric_add: float | int | list[float] | list[int] = 0,
    title="",
    shrink_width: float = 0.8,
    shrink_height: float = 1.0,
    ax=None,
):
    """Plot Dolan–Moré performance profiles for an arbitrary number of solver results.

    This function expects one or more ``SolverResult`` objects as positional
    arguments. Each ``SolverResult`` must contain a ``dataframe`` (indexed by
    instance identifier), a ``solver_name`` and a ``solver_id``. The helper
    locates metric and result columns in the merged dataframe using the
    convention ``{metric_col}{solver_id}`` and ``{result_col}{solver_id}``.

    Key behaviour:
    - All solver dataframes are outer-merged on their index (union of
      instances). Missing rows for a solver are treated as unsolved (``+inf``
      metric).
    - ``metric_cols`` may be a single string (used for every solver) or a list
      of strings (one per solver). The actual column looked up for solver i is
      ``f"{metric_cols[i]}{solver.solver_id}"``.
    - ``result_cols`` may be a single string, a list of strings (one per
      solver), or omitted. When provided, entries whose result is not in
      ``accepted_results`` are considered unsolved and their metric set to
      ``+inf``; the corresponding result columns are dropped from the merged
      table after this filtering.
    - ``metric_add`` (scalar or per-solver list) is added to metric values
      after loading; use to adjust units or add small epsilons.
    - The performance ratio for instance p and solver s is
      ``r_{p,s} = t_{p,s} / min_j t_{p,j}`` computed only over instances
      solved by at least one solver (i.e., where the best time is finite).

    Parameters
    ----------
    *results : SolverResult
        One or more SolverResult objects to compare.
    metric_cols : str or list[str], default "time"
        Metric column name(s) (base name). If a single string is provided it
        will be used for every solver; if a list is provided it must match the
        number of results. The final column looked up is formed by appending
        the solver's ``solver_id`` to the base name.
    result_cols : str or list[str], default "result"
        Result column name(s) (base name) used to determine whether a run is
        considered solved. Same shape rules as ``metric_cols`` apply.
    accepted_results : tuple[str], default ("sat", "unsat")
        Result labels considered as solved; other labels mark the run as
        unsolved (``+inf`` metric).
    max_tau : float or None
        Maximum x-axis ratio value for plotting. If ``None`` it is inferred
        from the observed finite ratios.
    num_points : int, default 200
        Number of tau points used to build the profile curves.
        columns when coercing. Kept for backward compatibility.
    metric_add : scalar or list, default 0
        Value added to metrics after loading; may be a scalar or a list with
        one entry per solver.
    ax : matplotlib.axes.Axes or None
        Optional axes to plot into. If ``None`` a new figure/axis are created.

    Returns
    -------
    ax : matplotlib.axes.Axes
        The axes containing the plotted performance profiles.
    profile_df : pandas.DataFrame
        DataFrame indexed by tau values with one column per solver containing
        the percentage of instances with ratio <= tau (values in 0..100).
    """
    if len(results) < 2:
        raise ValueError("At least two results are required")

    if result_cols is None:
        result_cols = None
    elif isinstance(result_cols, str):
        result_cols = [result_cols] * len(results)
    elif isinstance(result_cols, list) and len(result_cols) != len(results):
        raise ValueError("result_cols list must have same length as results")
    else:
        raise TypeError("result_cols must be either a string, a list of strings, or None")

    if isinstance(metric_cols, str):
        metric_cols = [metric_cols] * len(results)
    elif isinstance(metric_cols, list) and len(metric_cols) != len(results):
        raise ValueError("time_col list must have same length as dataframes")
    else:
        raise TypeError("time_col must be either a string or a list of strings")

    dataframes = (result.dataframe for result in results)
    df_all = reduce(
        lambda left, right: pd.merge(left, right, left_index=True, right_index=True, how="outer"), dataframes
    )
    # df_all.reset_index(inplace=True)

    for i, result in enumerate(results):
        solver_metric_col = f"{metric_cols[i]}{result.solver_id}"
        assert solver_metric_col in df_all, f"Column '{solver_metric_col}' not found for solver '{result.solver_name}'"
        df_all[solver_metric_col] = df_all[solver_metric_col].astype(float).fillna(np.inf)

        if metric_add != 0:
            df_all[solver_metric_col] += metric_add

        if result_cols is not None and len(accepted_results) > 0:
            solver_result_col = f"{result_cols[i]}{result.solver_id}"
            assert (
                solver_result_col in df_all
            ), f"Column '{solver_result_col}' not found for solver '{result.solver_name}'"
            df_all.loc[~df_all[solver_result_col].isin(accepted_results), [solver_metric_col]] = np.inf
            df_all.drop(solver_result_col, axis=1, inplace=True)

    best_time = df_all.min(axis=1, numeric_only=True)
    valid_instances = best_time < np.inf

    assert sum(valid_instances > 0) > 0, "No solved instances found across provided dataframes"

    ratios = df_all[valid_instances].div(best_time[valid_instances], axis=0)

    if max_tau is None:
        finite_ratios = ratios.replace([np.inf, -np.inf], np.nan).to_numpy().ravel()
        finite_ratios = finite_ratios[~np.isnan(finite_ratios)]
        inferred_max_tau = float(np.max(finite_ratios)) if finite_ratios.size > 0 else 1.0
        max_tau = max(1.0, inferred_max_tau)
    else:
        max_tau = max(1.0, float(max_tau))

    tau_values = np.linspace(1.0, max_tau, num_points)
    profile_df = pd.DataFrame(index=tau_values)

    for i, result in enumerate(results):
        solver_metric_col = f"{metric_cols[i]}{result.solver_id}"
        r = ratios[solver_metric_col].to_numpy()
        profile_df[result.solver_name] = [float(np.mean(r <= tau) * 100) for tau in tau_values]

    if ax is None:
        _, ax = plt.subplots()
    for result in results:
        ax.step(profile_df.index, profile_df[result.solver_name], where="post", label=result.solver_name)

    ax.set_xlabel("Ratio to best time (log scale)")
    ax.set_ylabel("Percentage of instances")
    if title:
        ax.set_title(title)
    ax.set_xlim(1.0, max_tau)
    ax.set_ylim(0.0, 100.0)
    ax.set_xscale(value="log")
    ax.grid(True, linestyle="--", alpha=0.4)
    ax.figure.tight_layout()

    box = ax.get_position()
    ax.set_position([box.x0, box.y0, box.width * shrink_width, box.height * shrink_height])

    # Put a legend to the right of the current axis
    ax.legend(loc='center left', bbox_to_anchor=(1, 0.5))

    return ax, profile_df


def plot_time_histogram(
    *results: SolverResult,
    metric_cols: str | list[str] = "time",
    result_cols: str | list[str] = "result",
    accepted_results: tuple[str, ...] = ("sat", "unsat"),
    bins: int | list[int] = 20,
    fixed_min_bin: float = 0.0,
    fixed_max_bin: float = None,
    title="Time histograms",
    ax=None,
):
    """Plot histograms of solving times for an arbitrary number of solver results.

    This function expects one or more ``SolverResult`` objects as positional
    arguments. Each ``SolverResult`` must contain a ``dataframe`` (indexed by
    instance identifier), a ``solver_name`` and a ``solver_id``. The helper
    locates metric and result columns in the merged dataframe using the
    convention ``{metric_col}{solver_id}`` and ``{result_col}{solver_id}``.

    Key behaviour:
    - All solver dataframes are outer-merged on their index (union of
      instances). Missing rows for a solver are treated as unsolved (``+inf``
      metric).
    - ``metric_cols`` may be a single string (used for every solver) or a list
      of strings (one per solver). The actual column looked up for solver i is
      ``f"{metric_cols[i]}{solver.solver_id}"``.
    - ``result_cols`` may be a single string, a list of strings (one per
      solver), or omitted. When provided, entries whose result is not in
      ``accepted_results`` are considered unsolved and their metric set to
      ``+inf``; the corresponding result columns are dropped from the merged
      table after this filtering.
    - ``metric_add`` (scalar or per-solver list) is added to metric values
      after loading; use to adjust units or add small epsilons.

    Parameters
    ----------
    *results : SolverResult
        One or more SolverResult objects to compare.
    metric_cols : str or list[str], default "time"
        Metric column name(s) (base name). If a single string is provided it
        will be used for every solver; if a list is provided it must match the
        number of results. The final column looked up is formed by appending
        the solver's ``solver_id`` to the base name.
    result_cols : str or list[str], default "result"
        Result column name(s) (base name) used to determine whether a run is
        considered solved. Same shape rules as ``metric_cols`` apply.
    accepted_results : tuple[str], default ("sat", "unsat")
        Result labels considered as solved; other labels mark the run as
        unsolved (``+inf`` metric).
    bins : int or list[int], default 20
        Number of bins for the histogram. If a single integer is provided it will
        be used for every solver; if a list is provided it must match the number
        of results.
    fixed_min_bin : float, default 0.0
        If provided, this value is used as the lower limit for the histogram bins
        for all solvers. If None, the minimum bin edge is inferred from the data.
    fixed_max_bin : float or None
        If provided, this value is used as the upper limit for the histogram bins
        for all solvers. If None, the maximum bin edge is inferred from the data.
    title : str, default "Time histograms"
        Title for the plot.
    ax : matplotlib.axes.Axes or None
        Optional axes to plot into. If ``None`` a new figure/axis are created.
    """
    if len(results) < 2:
        raise ValueError("At least two results are required")

    if result_cols is None:
        result_cols = None
    elif isinstance(result_cols, str):
        result_cols = [result_cols] * len(results)
    elif isinstance(result_cols, list) and len(result_cols) != len(results):
        raise ValueError("result_cols list must have same length as results")
    else:
        raise TypeError("result_cols must be either a string, a list of strings, or None")

    if isinstance(metric_cols, str):
        metric_cols = [metric_cols] * len(results)
    elif isinstance(metric_cols, list) and len(metric_cols) != len(results):
        raise ValueError("time_col list must have same length as dataframes")
    else:
        raise TypeError("time_col must be either a string or a list of strings")

    if isinstance(bins, int):
        bins = [bins] * len(results)
    elif isinstance(bins, list) and len(bins) != len(results):
        raise ValueError("bins list must have same length as results")
    else:
        raise TypeError("bins must be either an integer or a list of integers")

    dataframes = (result.dataframe for result in results)
    df_all = reduce(
        lambda left, right: pd.merge(left, right, left_index=True, right_index=True, how="outer"), dataframes
    )

    for i, result in enumerate(results):
        solver_metric_col = f"{metric_cols[i]}{result.solver_id}"
        assert solver_metric_col in df_all, f"Column '{solver_metric_col}' not found for solver '{result.solver_name}'"
        df_all[solver_metric_col] = df_all[solver_metric_col].astype(float).fillna(np.inf)

        if result_cols is not None and len(accepted_results) > 0:
            solver_result_col = f"{result_cols[i]}{result.solver_id}"
            assert (
                solver_result_col in df_all
            ), f"Column '{solver_result_col}' not found for solver '{result.solver_name}'"
            df_all.loc[~df_all[solver_result_col].isin(accepted_results), [solver_metric_col]] = np.inf
            df_all.drop(solver_result_col, axis=1, inplace=True)

    if fixed_min_bin is not None:
        min_bin = fixed_min_bin
    else:
        finite_times = df_all.replace([np.inf, -np.inf], np.nan).to_numpy().ravel()
        finite_times = finite_times[~np.isnan(finite_times)]
        min_bin = float(np.min(finite_times)) if finite_times.size > 0 else 0.0

    if fixed_max_bin is not None:
        max_bin = fixed_max_bin
    else:
        finite_times = df_all.replace([np.inf, -np.inf], np.nan).to_numpy().ravel()
        finite_times = finite_times[~np.isnan(finite_times)]
        max_bin = float(np.max(finite_times)) if finite_times.size > 0 else 1.0
    bin_edges = np.linspace(min_bin, max_bin, max(bins) + 1)

    if ax is None:
        _, ax = plt.subplots()
    for i, result in enumerate(results):
        solver_metric_col = f"{metric_cols[i]}{result.solver_id}"
        times = df_all[solver_metric_col].replace([np.inf, -np.inf], np.nan).dropna()
        ax.hist(times, bins=bin_edges, alpha=0.5, label=result.solver_name)
    ax.set_xlabel(r"Time (ms)")
    ax.set_ylabel(r"Number of instances")
    ax.yaxis.get_major_locator().set_params(integer=True)
    ax.set_title(title)
    ax.legend()
    return ax, bin_edges
