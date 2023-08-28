import os
import argparse
import configparser

SOLVERS = ["qsoptex", "soplex"]


def parse_command_line_args() -> "argparse.Namespace":
    def file(filename: "str") -> "str":
        if filename is not None and not os.path.exists(filename):
            raise argparse.ArgumentTypeError("{} does not exist".format(filename))
        return filename

    parser = argparse.ArgumentParser(description="Run dlinear on a smt2 file. Compare the results against a reference.")
    subparsers = parser.add_subparsers(required=True, help="command to perform", dest="command")

    # Produce the expected output using z3
    parser_z3 = subparsers.add_parser("z3", help="produce the expected output using z3")
    parser_z3.add_argument("--z3", type=str, help="z3 binary to run", default="z3")
    parser_z3.add_argument("smt2", type=file, help="smt2 file to run or directory containing smt2 files")

    # Benchmark dlinear
    parser_benchmark = subparsers.add_parser("benchmark", help="benchmark dlinear")
    parser_benchmark.add_argument("dlinear", type=file, help="dlinear binary to run")
    parser_benchmark.add_argument(
        "-s", "--solver", nargs="+", help="solver to use", default=["qsoptex"], choices=SOLVERS
    )
    parser_benchmark.add_argument("-p", "--precision", nargs="+", type=float, help="precision to use", default=[0.0001])
    parser_benchmark.add_argument(
        "-c",
        "--config_file",
        type=file,
        help="config file with the parameters to use. If set, it will override precision and solver",
        default=None,
    )

    args = parser.parse_args()
    apply_config_file(args)
    validate_command_line_args(args)
    return args


def validate_command_line_args(args: "argparse.Namespace"):
    if args.command == "z3":
        if not os.path.isdir(args.smt2) and not args.smt2.endswith(".smt2"):
            raise argparse.ArgumentTypeError("smt2 must be a directory or an smt2 file")
    elif args.command == "benchmark":
        if any(solver not in SOLVERS for solver in args.solver):
            raise argparse.ArgumentTypeError("solver must be one of {}. Found {}".format(SOLVERS, args.solver))
        if not os.path.isfile(args.dlinear) or not os.access(args.dlinear, os.X_OK):
            raise argparse.ArgumentTypeError("dlinear must be an executable file")
        if args.config_file is not None and not os.path.isfile(args.config_file):
            raise argparse.ArgumentTypeError("config_file must be a file")


def apply_config_file(args: "argparse.Namespace"):
    if args.config_file is None:
        return

    config = configparser.ConfigParser()
    config.read(args.config_file)
    solver = config.get("dlinear", "solver", fallback=None)
    precision = config.get("dlinear", "precision", fallback=None)

    if solver is not None:
        args.solver = solver.split()
    if precision is not None:
        args.precision = list(map(float, precision.split()))
