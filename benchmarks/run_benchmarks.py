#!/usr/bin/env python3
import argparse
import math
import os
import subprocess
import sys
from glob import glob
from pathlib import Path


class Args(argparse.Namespace):
    solver: str
    binary: "str | None"
    dir: str
    ext: str
    workers: int
    output_dir: "str | None"
    instances: "str | None"
    timeout: "int | None"
    local_limit: int
    iterations: int
    check_models: bool
    run_id: str
    task_id: int
    strict: bool
    delta: float
    skip_first_line: bool


# ---------------------------------------------------------------------------
# Input file discovery
# ---------------------------------------------------------------------------


def load_input_files(args: Args) -> list[str]:
    """Return a sorted list of benchmark file paths."""
    dir, ext, instances = args.dir, args.ext, args.instances
    if instances and Path(instances).is_file():
        with open(instances, "r", encoding="utf-8") as fh:
            files = [f"{args.instances_prefix}{line.strip()}" for line in fh if line.strip()]
            if args.skip_first_line:
                files = files[1:]
    else:
        pattern = os.path.join(dir, f"*.{ext}")
        files = sorted(glob(pattern))
    return files


# ---------------------------------------------------------------------------
# Solver runners
# ---------------------------------------------------------------------------


def run_cvc5(file: str, args: Args, output_dir: str) -> None:
    filename = Path(file).stem
    out_file = os.path.join(output_dir, f"{filename}.{args.solver}.expected")
    err_file = os.path.join(output_dir, f"{filename}.{args.solver}.stats")
    cmd = [args.binary or "cvc5", file, "--stats-all", "--stats-internal"]
    if args.timeout is not None:
        cmd.extend(["--tlimit-per", str(args.timeout * 1000)])  # cvc5 expects milliseconds
    with open(out_file, "w", encoding="utf-8") as out, open(err_file, "w", encoding="utf-8") as err:
        try:
            subprocess.run(cmd, stdout=out, stderr=err, timeout=args.timeout + 120 if args.timeout else None)
        except subprocess.TimeoutExpired:
            err.write(f"Error: Solver timed out after {args.timeout} seconds\n")


def run_glpk(file: str, args: Args, output_dir: str) -> None:
    filename = Path(file).stem
    out_file = os.path.join(output_dir, f"{filename}.{args.solver}.expected")
    err_file = os.path.join(output_dir, f"{filename}.{args.solver}.stats")
    cmd = [
        args.binary or "cvc5",
        file,
        "--use-approx",
        f"--standard-effort-variable-order-pivots={args.iterations}",
        "--stats-all",
        "--stats-internal",
    ]
    if args.timeout is not None:
        cmd.extend(["--tlimit-per", str(args.timeout * 1000)])  # cvc5 expects milliseconds
    with open(out_file, "w", encoding="utf-8") as out, open(err_file, "w", encoding="utf-8") as err:
        err.write(f"options::pivots = {args.iterations}\n")
        err.write(f"options::checkModels = {1 if args.check_models else 0}\n")
        err.write(f"options::external-lp-solver = {args.solver}\n")
        err.write(f"options::delta = {args.delta}\n")
        try:
            subprocess.run(cmd, stdout=out, stderr=err, timeout=args.timeout + 120 if args.timeout else None)
        except subprocess.TimeoutExpired:
            err.write(f"Error: Solver timed out after {args.timeout} seconds\n")


def run_soplex(file: str, args: Args, output_dir: str) -> None:
    filename = Path(file).stem
    out_file = os.path.join(output_dir, f"{filename}.{args.solver}.expected")
    err_file = os.path.join(output_dir, f"{filename}.{args.solver}.stats")
    cmd = [
        args.binary or "cvc5",
        file,
        "--use-approx",
        f"--standard-effort-variable-order-pivots={args.iterations}",
        f"--external-lp-solver={args.solver}",
        "--stats-all",
        "--stats-internal",
    ]
    if args.strict:
        cmd.append("--lp-strict-var")
    else:
        cmd.append("--no-lp-strict-var")
    if args.timeout is not None:
        cmd.extend(["--tlimit-per", str(args.timeout * 1000)])  # cvc5 expects milliseconds
    if args.delta >= 0:
        cmd.append(f"--delta={args.delta}")
    with open(out_file, "w", encoding="utf-8") as out, open(err_file, "w", encoding="utf-8") as err:
        err.write(f"options::pivots = {args.iterations}\n")
        err.write(f"options::checkModels = {1 if args.check_models else 0}\n")
        err.write(f"options::strict = {1 if args.strict else 0}\n")
        err.write(f"options::external-lp-solver = {args.solver}\n")
        err.write(f"options::delta = {args.delta}\n")
        try:
            subprocess.run(cmd, stdout=out, stderr=err, timeout=args.timeout + 120 if args.timeout else None)
        except subprocess.TimeoutExpired:
            err.write(f"Error: Solver timed out after {args.timeout} seconds\n")


def run_qsoptex(file: str, args: Args, output_dir: str) -> None:
    filename = Path(file).stem
    out_file = os.path.join(output_dir, f"{filename}.{args.solver}.expected")
    err_file = os.path.join(output_dir, f"{filename}.{args.solver}.stats")
    cmd = [
        args.binary or "cvc5",
        file,
        "--use-approx",
        f"--standard-effort-variable-order-pivots={args.iterations}",
        f"--external-lp-solver={args.solver}",
        "--stats-all",
        "--stats-internal",
    ]
    if args.strict:
        cmd.append("--lp-strict-var")
    else:
        cmd.append("--no-lp-strict-var")
    if args.timeout is not None:
        cmd.extend(["--tlimit-per", str(args.timeout * 1000)])  # cvc5 expects milliseconds
    if args.delta >= 0:
        cmd.append(f"--delta={args.delta}")
    with open(out_file, "w", encoding="utf-8") as out, open(err_file, "w", encoding="utf-8") as err:
        err.write(f"options::pivots = {args.iterations}\n")
        err.write(f"options::checkModels = {1 if args.check_models else 0}\n")
        err.write(f"options::strict = {1 if args.strict else 0}\n")
        err.write(f"options::external-lp-solver = {args.solver}\n")
        err.write(f"options::delta = {args.delta}\n")
        try:
            subprocess.run(cmd, stdout=out, stderr=err, timeout=args.timeout + 120 if args.timeout else None)
        except subprocess.TimeoutExpired:
            err.write(f"Error: Solver timed out after {args.timeout} seconds\n")


# ---------------------------------------------------------------------------
# Main execution logic
# ---------------------------------------------------------------------------

RUNNERS = {
    "cvc5": run_cvc5,
    "glpk": run_glpk,
    "soplex": run_soplex,
    "qsoptex": run_qsoptex,
}


def run_benchmark(idx: int, input_files: list[str], args: Args, output_dir: str) -> None:
    file = input_files[idx]
    print(f"Reading file {file}")
    RUNNERS[args.solver](file, args, output_dir)


def compute_output_dir(args: Args) -> str:
    """Determine the output directory from the arguments."""
    if args.output_dir:
        return args.output_dir
    if args.solver in ["soplex", "qsoptex"]:
        strict_flag = "_strict" if args.strict else ""
        delta_flag = f"_delta{args.delta}" if args.delta >= 0 else ""
        return f"{args.solver}_i{args.iterations}{strict_flag}{delta_flag}_TMP"
    if args.solver == "glpk":
        return f"{args.solver}_i{args.iterations}_TMP"
    return f"{args.solver}_smt_TMP"


def execute(args: Args) -> None:
    input_files = load_input_files(args)
    total_files = len(input_files)

    output_dir = compute_output_dir(args)
    os.makedirs(output_dir, exist_ok=True)

    if total_files == 0:
        print(f"No input files found in {args.dir} with extension .{args.ext}")
        sys.exit(1)

    if args.task_id == -1:
        # Local mode
        limit = min(args.local_limit, total_files)
        print(f"Local mode: running first {limit} benchmarks")
        for i in range(limit):
            run_benchmark(i, input_files, args, output_dir)
    else:
        # SLURM array mode
        workers = args.workers
        chunk_size = math.ceil(total_files / workers)
        start_idx = args.task_id * chunk_size
        end_idx = min(start_idx + chunk_size - 1, total_files - 1)

        if start_idx >= total_files:
            print(f"Worker {args.task_id} has no assigned benchmarks")
            sys.exit(0)

        print(f"Static chunk mode with {workers} workers over {total_files} benchmarks")
        print(f"Worker {args.task_id} running indices {start_idx}..{end_idx}")
        for i in range(start_idx, end_idx + 1):
            run_benchmark(i, input_files, args, output_dir)
        print(f"Worker {args.task_id} finished")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Unified benchmark runner for SMT solvers.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=__doc__,
    )

    # ---- Positional: solver choice ----
    parser.add_argument(
        "solver",
        choices=["cvc5", "soplex", "qsoptex", "glpk"],
        help="Solver to run.",
    )

    # ---- General options ----
    parser.add_argument(
        "--binary",
        default=None,
        help="Path to the solver binary. Defaults: cvc5 → './cvc5-original, soplex → './cvc5', glpk → './cvc5-fix.",
    )
    parser.add_argument(
        "--dir",
        default="/nobackup/proj/comet_lfplpsmf/QF_LRA/all",
        help="Directory containing benchmark files (default: %(default)s).",
    )
    parser.add_argument(
        "--ext",
        default="smt2",
        help="Benchmark file extension (default: %(default)s).",
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=128,
        help="Number of SLURM array workers (default: %(default)s).",
    )
    parser.add_argument(
        "--output-dir",
        default=None,
        help="Output directory.  Defaults: '<solver>_i<iterations>_<strict>_<delta>'.",
    )
    parser.add_argument(
        "--instances",
        default=None,
        help="Path to a file listing benchmark instances (one per line).",
    )
    parser.add_argument(
        "--timeout",
        type=int,
        default=None,
        help="Per-instance timeout in seconds (solver-enforced).",
    )
    parser.add_argument(
        "--local-limit",
        type=int,
        default=6,
        help="Number of benchmarks to run in local (non-SLURM) mode (default: %(default)s).",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        default=False,
        help="Enable strict mode for soplex (if applicable).",
    )
    parser.add_argument(
        "--delta",
        type=float,
        default=-1.0,
        help="Delta value for approximation (if applicable).",
    )
    parser.add_argument(
        "--skip-first-line",
        action="store_true",
        default=False,
        help="Skip the first line of the instances file (useful if it contains a header).",
    )
    parser.add_argument(
        "--instances-prefix",
        default="",
        help="Prefix to add to each instance path read from the instances file (default: %(default)s).",
    )

    # ---- cvc5-specific options ----
    cvc5_group = parser.add_argument_group("cvc5 options")
    cvc5_group.add_argument(
        "--iterations",
        type=int,
        default=-1,
        help="standard-effort-variable-order-pivots value (default: %(default)s).",
    )
    cvc5_group.add_argument(
        "--check-models",
        action="store_true",
        default=False,
        help="Enable --check-models for cvc5.",
    )

    # ---- SLURM submission options ----
    slurm_group = parser.add_argument_group("SLURM submission options")
    slurm_group.add_argument(
        "--task-id",
        type=int,
        default=-1,
        help="SLURM array task ID (automatically detected from environment).",
    )

    return parser


def main() -> None:
    parser = build_parser()
    args: Args = parser.parse_args()
    if args.solver in ("soplex", "glpk", "qsoptex") and args.iterations <= 0:
        print("Error: --iterations must be > 0 when using soplex, glpk or qsoptex.")
        sys.exit(1)

    execute(args)


if __name__ == "__main__":
    main()
