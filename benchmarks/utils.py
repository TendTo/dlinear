import subprocess
import re
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass
from itertools import combinations, product
from functools import reduce
import random
from pathlib import Path

def is_docker():
    cgroup = Path('/proc/self/cgroup')
    return Path('/work/.dockerenv').is_file() or (cgroup.is_file() and 'docker' in cgroup.read_text())

SAVE = not is_docker()

GLPK = 1
SOPLEX = 2
QSOPTEX = 3

plt.rcParams.update(
    {
        "text.usetex": True,
        "font.size": 10,
        "axes.titlesize": 12,
        "axes.labelsize": 10,
        "legend.fontsize": 10,
        "xtick.labelsize": 10,
        "ytick.labelsize": 10,
        "font.family": "serif",
        "font.serif": ["Times New Roman"],
        "figure.figsize": (12.19826 / 2.54, 6.5 / 2.54),  # Convert from cm to inches
    }
)


@dataclass
class SolverResult:
    dataframe: pd.DataFrame
    solver_name: str
    solver_id: str
    iterations: int = -1

    @staticmethod
    def empty():
        return SolverResult(dataframe=pd.DataFrame(), solver_name="", solver_id="")

    @property
    def result_key(self) -> str:
        return f"result{self.solver_id}"

    def apply_filter(self, filter_func):
        return SolverResult(
            dataframe=filter_func(self.dataframe),
            solver_name=self.solver_name,
            solver_id=self.solver_id,
            iterations=self.iterations,
        )

    def replace_df(self, new_df: pd.DataFrame):
        return SolverResult(
            dataframe=new_df, solver_name=self.solver_name, solver_id=self.solver_id, iterations=self.iterations
        )


def difficulty_analysis(solvers_analysis: list[SolverResult], total_count: int, group_name="all"):
    # Instance difficulty categorization
    text = f"""## Difficulty analysis on {group_name}

All problems are divided into buckets depending on the time taken by the solver to solve them.

| Solver | Strict | Pivots | Very Fast (<0.1s) | Fast (0.1-1s) | Medium (1-10s) | Hard (10-100s) | Very Hard (>100s) | Total |
| ------ | ------ | ------ | ----------------- | ------------- | -------------- | -------------- | ----------------- | ----- |
"""

    # Categorize instances by time range
    def categorize_time(time_val):
        if time_val < 0.1:
            return "Very Fast (<0.1s)"
        elif time_val < 1:
            return "Fast (0.1-1s)"
        elif time_val < 10:
            return "Medium (1-10s)"
        elif time_val < 100:
            return "Hard (10-100s)"
        else:
            return "Very Hard (>100s)"

    # Analyze institution distribution for each solver

    rows = []
    data = {}

    categories = ["Very Fast (<0.1s)", "Fast (0.1-1s)", "Medium (1-10s)", "Hard (10-100s)", "Very Hard (>100s)"]
    latex_categories = ["$[0s, 0.1s)$", "$[0.1s, 1s)$", "$[1s, 10s)$", "$[10s, 100s)$", r"$[100s, 6h)$"]
    for solver in solvers_analysis:
        if solver.dataframe.empty:
            continue
        solver_name = solver.solver_name
        df = solver.dataframe
        solver_id = solver.solver_id
        df_copy = (
            df.copy()
            if "theory::arith::z::arith::relax::calls" not in df.columns
            else df[df["theory::arith::z::arith::relax::calls"] > 0].copy()
        )
        df_copy = df_copy[df_copy[f"result{solver_id}"].isin(["sat", "unsat"])]

        df_copy["category"] = df_copy[f"time{solver_id}"].apply(categorize_time)
        assert (
            len(df_copy["options::pivots"].unique()) == 1 if "options::pivots" in df_copy.columns else True
        ), f"Expected only one pivot limit per solver in the analysis, but got {df_copy['options::pivots'].unique()} on solver {solver_name}"
        pivot_limit = int(df_copy["options::pivots"].iloc[0]) if "options::pivots" in df_copy.columns else 0

        row = f"| {solver_name} | {'✔' if "options::strict" in df_copy.columns and  df_copy['options::strict'].iloc[0] else ''} | {pivot_limit}"

        data[solver_name] = {
            r"\# Sol. / \# Tot.": f"{len(df_copy)} / {total_count} ({100 * len(df_copy) / total_count:.1f}\\%)"
        }
        data[solver_name]["solved"] = len(df_copy)
        data[solver_name]["total"] = total_count

        for category, latex_category in zip(categories, latex_categories):
            count = (df_copy["category"] == category).sum()
            if count > 0:
                pct = 100 * count / len(df_copy)
                row += f" | {count} ({pct:.1f}%)"
            else:
                row += " | 0"
            data[solver_name][latex_category] = int(count)
        row += f" | {len(df_copy)} / {total_count} ({100 * len(df_copy) / total_count:.1f}%)"
        rows.append(row)

    if len(data) == 0:
        return "No data available for difficulty analysis."

    data_df = pd.DataFrame(data).T
    for col in data_df.columns:
        if col != r"\# Sol. / \# Tot.":
            data_df[col] = data_df[col].fillna(0).astype(int)
    data_df.sort_values(by=["solved"] + latex_categories, inplace=True, ascending=False)


    ax = data_df[latex_categories].plot(
        kind="bar",
        stacked=True,
        colormap="tab20",
    )
    ax.set_ylabel("Solved instances")
    ax.grid(axis="y", alpha=0.3)
    plt.xticks(rotation=25, ha="center")
    plt.tight_layout()
    box = ax.get_position()
    ax.set_position([box.x0, box.y0, box.width * 0.8, box.height * 0.8])

    # Put a legend to the right of the current axis
    ax.legend(title="Category", loc="center left", bbox_to_anchor=(1, 0.5))
    plt.show()


    return f"""{text}{"\n".join(rows)}
"""


def external_solver_impact(solvers_analysis: list[SolverResult], filename: str = ""):
    # Instance difficulty categorization
    text = """## External solver impact

Analysis on the impact of the external simplex solver on the overall performance of the SMT solver, based on the number of calls to the external simplex and the techniques used to obtain the exact solution (precision boosting and iterative refinements).
    
| Solver | Calls |"""
    precisions = set()
    refinements = set()

    solvers_analysis = [
        (
            solver.solver_name,
            solver.dataframe[solver.dataframe[f"result{solver.solver_id}"].isin(["sat", "unsat"])],
            solver.solver_id,
        )
        for solver in solvers_analysis
        if "theory::arith::z::arith::relax::calls" in solver.dataframe.columns
    ]

    data = {}

    for solver_name, df, solver_id in solvers_analysis:
        assert "theory::arith::z::arith::relax::calls" in df.columns
        assert df[f"result{solver_id}"].isin(["sat", "unsat"]).all()
        for col in df.columns:
            if col.startswith("precision_") and df[col].sum() > 0:
                precisions.add(col[len("precision_") :])
        for col in df.columns:
            if col.startswith("refinements_") and df[col].sum() > 0:
                refinements.add(col[len("refinements_") :])

    precisions = sorted(precisions, key=lambda x: int(x))
    refinements = sorted(refinements, key=lambda x: int(x))

    for precision in precisions:
        text += f" $p_{{{precision}}}$ |"
    for refinement in refinements:
        text += f" $r_{{{refinement}}}$ |"

    text += "\n| ------ | ----- |"

    for precision in precisions:
        text += f" {'-' * 3} |"
    for refinement in refinements:
        text += f" {'-' * 3} |"

    text += "\n"

    for solver_name, df, solver_id in solvers_analysis:

        calls = int(df["theory::arith::z::arith::relax::calls"].sum())

        # Consistency checks requested: present precision/refinement counters should sum to calls.
        precision_cols = [c for c in df.columns if c.startswith("precision_")]
        refinement_cols = [c for c in df.columns if c.startswith("refinements_")]

        if precision_cols:
            precision_sum = int(df[precision_cols].sum().sum())
            assert precision_sum == calls, (
                f"Precision totals do not match calls for {solver_name}: "
                f"precision_sum={precision_sum}, calls={calls}"
            )
        if refinement_cols:
            refinement_sum = int(df[refinement_cols].sum().sum())
            assert refinement_sum == calls, (
                f"Refinement totals do not match calls for {solver_name}: "
                f"refinement_sum={refinement_sum}, calls={calls}"
            )

        row = f"| {solver_name} | {calls} |"
        for precision in precisions:
            if f"precision_{precision}" in df.columns:
                row += f" {int(df[f'precision_{precision}'].sum())} |"
            else:
                row += " |"
        for refinement in refinements:
            if f"refinements_{refinement}" in df.columns:
                row += f" {int(df[f'refinements_{refinement}'].sum())} |"
            else:
                row += " |"
        data[solver_name] = {
            r"\# Calls": calls,
            **{
                f"$p_{{{precision}}}$": int(df[f"precision_{precision}"].sum())
                for precision in precisions
                if f"precision_{precision}" in df.columns
            },
            **{
                f"$r_{{{refinement}}}$": int(df[f"refinements_{refinement}"].sum())
                for refinement in refinements
                if f"refinements_{refinement}" in df.columns
            },
        }
        text += row + "\n"

    df = pd.DataFrame(data).T
    for col in df.columns:
        df[col] = df[col].fillna(0).astype(int)

    # Keep a numeric copy for plotting before turning empty values into strings for LaTeX aesthetics.
    plot_df = df.copy()

    # Plot precision/refinement contributions and compare against calls with dotted markers.
    precision_plot_cols = [f"$p_{{{precision}}}$" for precision in precisions]
    refinement_plot_cols = [f"$r_{{{refinement}}}$" for refinement in refinements]

    fig, axes = plt.subplots(1, 2, figsize=(13, 4), sharey=True)

    # Precision subplot.
    ax_p = axes[0]
    if precision_plot_cols:
        precision_df = plot_df[[r"\# Calls"] + precision_plot_cols].sort_values(by=r"\# Calls")
        # Show only bars with non-zero precision contribution.
        precision_df = precision_df[precision_df[precision_plot_cols].sum(axis=1) > 0]
        if len(precision_df) > 0:
            precision_df[precision_plot_cols].plot(
                kind="bar",
                stacked=True,
                colormap="tab20",
                ax=ax_p,
                legend=False,
            )
            bar_width = 0.8
            for i, calls in enumerate(precision_df[r"\# Calls"].astype(float).to_numpy()):
                ax_p.hlines(
                    y=calls,
                    xmin=i - bar_width / 2,
                    xmax=i + bar_width / 2,
                    colors="black",
                    linestyles="dotted",
                    linewidth=1.2,
                    zorder=5,
                )
        else:
            ax_p.text(0.5, 0.5, "No non-zero precision bars", ha="center", va="center", transform=ax_p.transAxes)
            ax_p.set_xticks([])
    else:
        ax_p.text(0.5, 0.5, "No precision columns", ha="center", va="center", transform=ax_p.transAxes)
        ax_p.set_xticks([])

    ax_p.set_title("Precision contributions")
    ax_p.set_xlabel("Solver")
    ax_p.set_ylabel("Calls")
    ax_p.grid(axis="y", alpha=0.3)
    ax_p.tick_params(axis="x", labelrotation=25)

    # Refinement subplot.
    ax_r = axes[1]
    if refinement_plot_cols:
        refinement_df = plot_df[[r"\# Calls"] + refinement_plot_cols].sort_values(by=r"\# Calls")
        # Show only bars with non-zero refinement contribution.
        refinement_df = refinement_df[refinement_df[refinement_plot_cols].sum(axis=1) > 0]
        if len(refinement_df) > 0:
            refinement_df[refinement_plot_cols].plot(
                kind="bar",
                stacked=True,
                colormap="tab20",
                ax=ax_r,
                legend=False,
            )
            bar_width = 0.8
            for i, calls in enumerate(refinement_df[r"\# Calls"].astype(float).to_numpy()):
                ax_r.hlines(
                    y=calls,
                    xmin=i - bar_width / 2,
                    xmax=i + bar_width / 2,
                    colors="black",
                    linestyles="dotted",
                    linewidth=1.2,
                    zorder=5,
                )
        else:
            ax_r.text(0.5, 0.5, "No non-zero refinement bars", ha="center", va="center", transform=ax_r.transAxes)
            ax_r.set_xticks([])
    else:
        ax_r.text(0.5, 0.5, "No refinement columns", ha="center", va="center", transform=ax_r.transAxes)
        ax_r.set_xticks([])

    ax_r.set_title("Refinement contributions")
    ax_r.set_xlabel("Solver")
    ax_r.grid(axis="y", alpha=0.3)
    ax_r.tick_params(axis="x", labelrotation=25)

    # Build a combined legend once.
    handles, labels = [], []
    for ax in axes:
        h, l = ax.get_legend_handles_labels()
        handles.extend(h)
        labels.extend(l)
    if handles:
        by_label = dict(zip(labels, handles))
        fig.legend(
            by_label.values(),
            by_label.keys(),
            title="Category",
            ncols=3,
            loc="upper center",
            bbox_to_anchor=(0.5, 1.08),
        )

    fig.suptitle("Exact solver impact (dotted line = calls)")
    plt.tight_layout()
    plt.show()

    return text


def print_stats(soplex_configs: list[SolverResult], filename: str = ""):
    summary_stats = {}
    for solver_result in soplex_configs:
        df = solver_result.dataframe
        if df.empty:
            continue
        assert all(df["theory::arith::z::arith::relax::calls"] > 0)

        df = df.copy()
        df["global::totalTime"] = df["global::totalTime"].apply(convert_to_numeric) / 1000
        df["theory::arith::z::approx::lp::timer"] = df["theory::arith::z::approx::lp::timer"].apply(convert_to_numeric) / 1000
        df["theory::arith::z::approx::lp::setup::timer"] = (
            df["theory::arith::z::approx::lp::setup::timer"].apply(convert_to_numeric)
            if "theory::arith::z::approx::lp::setup::timer" in df.columns
            else pd.Series(0, index=df.index)
        ) / 1000

        solved_df = pd.DataFrame()
        unknown_df = pd.DataFrame()
        if "resultS" in df.columns:
            solved_df = df[df["resultS"].isin(["sat", "unsat"])]
            unknown_df = df[~df["resultS"].isin(["sat", "unsat"])]
        if "resultQ" in df.columns:
            solved_df = df[df["resultQ"].isin(["sat", "unsat"])]
            unknown_df = df[~df["resultQ"].isin(["sat", "unsat"])]
        if "resultG" in df.columns:
            solved_df = df[df["resultG"].isin(["sat", "unsat"])]
            unknown_df = df[~df["resultG"].isin(["sat", "unsat"])]

        external_calls = len(df)
        solved = len(solved_df)
        unknown = len(unknown_df)
        feasible_failures = df[df["theory::arith::z::arith::relax::feasible::failures"] > 0].shape[0]
        infeasible_failures = df[df["theory::arith::z::arith::relax::infeasible::failures"] > 0].shape[0]

        avg_time_external = df["global::totalTime"].median() if external_calls > 0 else 0
        tot_time_external = df["global::totalTime"].sum() if external_calls > 0 else 0
        time_variance_external = df["global::totalTime"].var() if external_calls > 0 else 0
        lp_time = df["theory::arith::z::approx::lp::timer"].median() if external_calls > 0 else 0
        lp_setup_time = df["theory::arith::z::approx::lp::setup::timer"].median() if external_calls > 0 else 0

        adjustment_calls = int(
            df[df["theory::arith::z::approx::externalAdjustmentPivots"] > 0][
                "theory::arith::z::approx::externalAdjustmentPivots"
            ].sum()
            if "theory::arith::z::approx::externalAdjustmentPivots" in df.columns
            else -1
        )

        at_least_one_adjustment_call = (
            df[df["theory::arith::z::approx::externalAdjustmentPivots"] > 0].shape[0]
            if "theory::arith::z::approx::externalAdjustmentPivots" in df.columns
            else -1
        )

        avg_adjustment_calls = (
            df[df["theory::arith::z::approx::externalAdjustmentPivots"] > 0][
                "theory::arith::z::approx::externalAdjustmentPivots"
            ].median()
            if "theory::arith::z::approx::externalAdjustmentPivots" in df.columns and adjustment_calls > 0
            else -1
        )

        summary_stats[solver_result.solver_name] = {
            "solved": solved,
            "unknown": unknown,
            "external_calls": external_calls,
            "feasible_failures": feasible_failures,
            "infeasible_failures": infeasible_failures,
            "avg_time_external": avg_time_external,
            "tot_time_external": tot_time_external,
            "time_variance_external": time_variance_external,
            "lp_time": lp_time,
            "lp_setup_time": lp_setup_time,
            "adjustment_calls": adjustment_calls,
            "avg_adjustment_calls": avg_adjustment_calls,
            "at_least_one_adjustment_call": at_least_one_adjustment_call,
        }

    summary_df = pd.DataFrame(summary_stats).T
    summary_df["external_calls"] = summary_df["external_calls"].astype(int)
    summary_df["unknown"] = summary_df["unknown"].astype(int)
    summary_df["solved"] = summary_df["solved"].astype(int)
    summary_df["feasible_failures"] = summary_df["feasible_failures"].astype(int)
    summary_df["infeasible_failures"] = summary_df["infeasible_failures"].astype(int)
    summary_df["adjustment_calls"] = summary_df["adjustment_calls"].astype(int)
    summary_df["avg_adjustment_calls"] = summary_df["avg_adjustment_calls"].astype(int)
    summary_df["at_least_one_adjustment_call"] = summary_df["at_least_one_adjustment_call"].astype(int)
    summary_df["lp_setup_time"] = summary_df["lp_setup_time"].astype(float)
    summary_df["lp_time"] = summary_df["lp_time"].astype(float)
    renames = {
        # "solved": "Solved",
        # "unknown": "Unknown",
        "external_calls": r"\# Inst.",
        # "avg_time_external": "Med. Time (s)",
        # "adjustment_calls": "Adjustment Pivots",
        "lp_setup_time": "Setup Time (s)",
        "lp_time": "Run Time (s)",
        "avg_adjustment_calls": "Adj. Piv.",
        "at_least_one_adjustment_call": r"\# Adj. Piv. $\ge1$",
    }

    rows = []
    for config_name in summary_df.index:
        row = summary_df.loc[config_name]
        # failures = int(row["feasible_failures"] + row["infeasible_failures"])
        rows.append(
            f"| {config_name} | {int(row['external_calls'])} | {int(row['solved'])} | {int(row['unknown'])} | {int(row['tot_time_external'])} | {row['avg_time_external']:<15.2f}  | {row['lp_time']:<15.2f} | {row['lp_setup_time']:<15.2f} | {int(row['adjustment_calls'])} | {row['avg_adjustment_calls']:<15.2f} | {int(row['at_least_one_adjustment_call'])} |"
        )
    return f"""### Summary statistics by SoPlex pivot limit
| Config       | Registered results | Solved | Unknown | Tot Time | Med Time | Med LP Time | Med LP Setup Time | Adjustment calls | Med Adjustment calls | $>1$ Adj. Pivot |
| ------------ | -------------- | ------ | ------- | ---------- | --------- | ---- | ---- | ---------------- | ---------------------- | ----------------- |
{"\n".join(rows)}
    """


def write_instances(instances_100: pd.DataFrame, instances_200: pd.DataFrame, instances_300: pd.DataFrame):
    instances_100_list = instances_100.index.tolist()
    random.seed(42)
    random.shuffle(instances_100_list)
    with open("100_instances.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(f"/nobackup/proj/comet_lfplpsmf/QF_LRA/all/{u}" for u in instances_100_list))
    instances_200_list = instances_200.index.tolist()
    random.seed(42)
    random.shuffle(instances_200_list)
    with open("200_instances.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(f"/nobackup/proj/comet_lfplpsmf/QF_LRA/all/{u}" for u in instances_200_list))
    instances_300_list = instances_300.index.tolist()
    random.seed(42)
    random.shuffle(instances_300_list)
    with open("300_instances.txt", "w", encoding="utf-8") as f:
        f.write("\n".join(f"/nobackup/proj/comet_lfplpsmf/QF_LRA/all/{u}" for u in instances_300_list))


def sanitize(df: pd.DataFrame):
    if df.empty:
        return df

    df = df.copy()
    df = df[df["theory::arith::z::arith::relax::calls"] > 0]
    if df.empty:
        return df
    for col in df.columns:
        df[col] = df[col].apply(convert_to_numeric)

    if "theory::arith::z::approx::deltaResults" not in df.columns:
        df["theory::arith::z::approx::deltaResults"] = 0
    if "theory::arith::z::approx::delta" not in df.columns:
        df["theory::arith::z::approx::delta"] = -1
    if "options::delta" not in df.columns:
        df["options::delta"] = -1.0
    df["theory::arith::z::approx::externalSimplexType"] = (
        df["theory::arith::z::approx::externalSimplexType"]
        .map({SOPLEX: "SOPLEX", GLPK: "GLPK", QSOPTEX: "QSOPTEX"})
        .astype("category")
    )
    if "resultS" in df.columns:
        df["result"] = df["resultS"]
    elif "resultG" in df.columns:
        df["result"] = df["resultG"]
    elif "resultQ" in df.columns:
        df["result"] = df["resultQ"]
    else:
        raise KeyError("No result column found with expected suffixes 'S', 'G', or 'Q'")

    precision_df = df["theory::arith::z::approx::precision"].apply(lambda x: split_dict_columns(x, "precision"))
    refinements = df["theory::arith::z::approx::refinements"].apply(lambda x: split_dict_columns(x, "refinements"))

    # All instances with at least a call to the external simplex should have a value for the external simplex type
    assert (
        len(
            df[
                (df["theory::arith::z::arith::relax::calls"] > 0)
                & (df["theory::arith::z::approx::externalSimplexType"].isna())
            ]
        )
        == 0
    )
    assert all(df["theory::arith::z::arith::relax::calls"] > 0)
    assert len(df[df["theory::arith::z::approx::externalSimplexType"].notna()]) == len(
        df[(df["theory::arith::z::arith::relax::calls"] > 0)]
    )
    assert df["theory::arith::z::approx::externalSimplexType"].nunique() == 1
    return pd.concat([df, precision_df, refinements], axis=1)


def parse_duration_to_ms(value: str):
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
    zoom_max_tau: float | None = None,
    title="",
    shrink_width: float = 1.1,
    shrink_height: float = 0.8,
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
    elif isinstance(result_cols, list):
        if len(result_cols) != len(results):
            raise ValueError("result_cols list must have same length as results")
    else:
        raise TypeError("result_cols must be either a string, a list of strings, or None")

    if isinstance(metric_cols, str):
        metric_cols = [metric_cols] * len(results)
    elif isinstance(metric_cols, list):
        if len(metric_cols) != len(results):
            raise ValueError("metric_cols list must have same length as results")
    else:
        raise TypeError("metric_cols must be either a string or a list of strings")

    if isinstance(metric_add, (int, float)):
        metric_add = [metric_add] * len(results)
    elif isinstance(metric_add, list):
        if len(metric_add) != len(results):
            raise ValueError("metric_add list must have same length as results")
    else:
        raise TypeError("metric_add must be either a number or a list of numbers")

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
            df_all[solver_metric_col] += metric_add[i]

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
        current_figsize = plt.rcParams.get("figure.figsize")
        new_figsize = (current_figsize[0] / shrink_width, current_figsize[1] / (shrink_height + 0.1))
        _, ax = plt.subplots(figsize=new_figsize)

    # Black-and-white-friendly styling: cycle line styles and markers so that
    # curves stay distinguishable even when colors are not.
    line_styles = ["-", "--", ":", "-."]
    # Marker choice intentionally avoids very small/ambiguous markers.
    markers = ["o", "s", "^", "D", "v", ">", "<", "P", "X", "*"]
    style_cycle = list(product(line_styles, markers))

    plotted_lines = []
    for i, result in enumerate(results):
        linestyle, marker = style_cycle[i % len(style_cycle)]
        # markevery keeps the plot readable with many points.
        (line,) = ax.semilogx(
            profile_df.index,
            profile_df[result.solver_name],
            # where="post",
            label=result.solver_name,
            linestyle=linestyle,
            marker=marker,
            markersize=2.5,
            markevery=0.1,
            linewidth=1.3,
        )
        plotted_lines.append((result.solver_name, line))

    ax.set_xlabel("Ratio to best time (log scale)")
    ax.set_ylabel("Percentage of instances")
    if title:
        ax.set_title(title)
    ax.set_xlim(1.0, max_tau)
    ax.set_ylim(0.0, 100.0)
    ax.grid(True, linestyle="--", alpha=0.4)

    ax_zoom = ax.inset_axes([1.1, 0.0, 0.2, 1.0])

    zoom_max_tau = float(zoom_max_tau or max_tau)
    zoom_df = profile_df.loc[profile_df.index <= zoom_max_tau]
    for i, result in enumerate(results):
        linestyle, marker = style_cycle[i % len(style_cycle)]
        ax_zoom.plot(
            zoom_df.index,
            zoom_df[result.solver_name],
            linestyle=linestyle,
            marker=marker,
            markersize=2.5,
            markevery=0.1,
            linewidth=1.3,
        )

    ax_zoom.set_xlim(zoom_max_tau - zoom_max_tau / 10, zoom_max_tau)
    ax_zoom.set_ylim(profile_df.loc[zoom_max_tau].min() - 2, profile_df.loc[zoom_max_tau].max() + 2)
    ax_zoom.yaxis.set_label_position("right")
    ax_zoom.yaxis.tick_right()
    ax_zoom.grid(True, linestyle="--", alpha=0.4)

    inset_indicator = ax.indicate_inset_zoom(ax_zoom)
    for i, line in enumerate(inset_indicator.connectors):
        if i == 0 or i == 3:
            line.set_linestyle("--")
            line.set_color("gray")
            line.set_alpha(0.8)
            line.set_visible(True)
        else:
            line.set_visible(False)

    # Legend: place at top, with at most 2 rows.
    handles, labels = ax.get_legend_handles_labels()
    n_items = len(labels)
    if n_items > 0:
        import math

        ncol = n_items if n_items <= 5 else int(math.ceil(n_items / 2))
        ax.figure.legend(
            handles,
            labels,
            loc="upper center",
            bbox_to_anchor=(0.5, 1.015),
            ncol=ncol,
            # frameon=False,
        )

    ax.figure.tight_layout()

    box = ax.get_position()
    ax.set_position([box.x0, box.y0, box.width * shrink_width, box.height * shrink_height])

    # Put a legend to the right of the current axis
    # ax.legend(loc="center left", bbox_to_anchor=(1, 0.5))

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
