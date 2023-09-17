#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Run dlinear on a smt2 file. Compare the results against a reference.
By default, the reference is the .expected file in the same directory as the smt2 file.

With "name of the file" we mean the name of the file without the extension.
The name of the output file is built using the following rules in order:

- If the solver is not in continuous mode:
    1. The same name of the file with the extension .%solver.expected_phase_%n
        (e.g. smt2/input.smt2 -> smt2/input.soplex.expected_phase_1 for phase 1)
        (e.g. smt2/input.smt2 -> smt2/input.qsoptex.expected_phase_2 for phase 2 and qsoptex)
    2. The same name of the file with the extension .%solver.expected
        (e.g. smt2/input.smt2 -> smt2/input.soplex.expected)
    3. The same name of the file with the extension .expected_phase_%n
        (e.g. smt2/input.smt2 -> smt2/input.expected_phase_1 for phase 1)
        (e.g. smt2/input.smt2 -> smt2/input.expected_phase_2 for phase 2)
    4. The same name of the file with the extension .expected
        (e.g. smt2/input.smt2 -> smt2/input.expected)
    5. Raise an error if no reference file is found
- If the solver is in continuous mode:
    1. The same name of the file with the extension .expected_continuous_phase_%n
        (e.g. smt2/input.smt2 -> smt2/input.expected_continuous_phase_1 for phase 1)
        (e.g. smt2/input.smt2 -> smt2/input.expected_continuous_phase_2 for phase 2)
    2. The same name of the file with the extension .expected_continuous
        (e.g. smt2/input.smt2 -> smt2/input.expected_continuous)
    3. Skip the test if no reference file is found

Usage: TestSolver.py dlinear file lp_solver phase cont_mode [options]

Example: TestSolver.py ./dlinear smt2/input.smt2 qsoptex 1 False N
The above command will run dlinear on the input file with qsoptex, phase 1, SoPlex disabled, and no continuous mode.
The output will be compared against smt2/input.expected
"""
import sys
import os
import subprocess
import difflib
import argparse
import logging

logging.basicConfig(level=logging.DEBUG, format='%(asctime)s %(levelname)s %(message)s')
logger = logging.getLogger(__name__)


def parse_command_line_args() -> "argparse.Namespace":
    def file(filename: "str") -> "str":
        if not os.path.exists(filename):
            raise argparse.ArgumentTypeError("{} does not exist".format(filename))
        return filename

    parser = argparse.ArgumentParser(description="Run dlinear on an input file. Compare the results against a reference.")
    parser.add_argument("dlinear", type=file, help="dlinear binary to run")
    parser.add_argument("file", type=file, help="input file to test")
    parser.add_argument("lp_solver", help="which LP solver to use", choices=["soplex", "qsoptex"])
    parser.add_argument("phase", help="simplex phase", choices=["1", "2"])
    parser.add_argument("cont_mode",
                        help="""continuous mode.
                        | N -> no continuous mode | Y -> continuous mode | X -> continuous mode with exhaustive""",
                        choices=["N", "Y", "X"])
    parser.add_argument("options", nargs=argparse.REMAINDER, help="options to pass through to solver")
    parser.add_argument("--log-level", default="INFO", help="log level",
                        choices=["DEBUG", "INFO", "WARNING", "ERROR", "CRITICAL"])

    parsed_args = parser.parse_args()

    if parsed_args.cont_mode != "N" and parsed_args.lp_solver == "soplex":
        parser.error("Only qsoptex supports continuous mode")
    logger.setLevel(parsed_args.log_level)

    return parsed_args


def parse_dlinear_args(parsed_args: "argparse.Namespace") -> "list[str]":
    args = ["--simplex-sat-phase", parsed_args.phase, "--lp-solver", parsed_args.lp_solver]
    if parsed_args.cont_mode != "N":
        args.append("--continuous-output")
        if parsed_args.cont_mode == "X":
            args.append("--exhaustive")
    args.extend(parsed_args.options)
    return args


def get_expected_output(parsed_args: "argparse.Namespace") -> "list[str]":
    file_name = os.path.splitext(parsed_args.file)[0]
    if parsed_args.cont_mode == "N":
        expected_output_filenames = (
            "{}.{}.expected_phase_{}".format(file_name, parsed_args.lp_solver, parsed_args.phase),  # 1. (non-continuous mode)
            "{}.{}.expected".format(file_name, parsed_args.lp_solver),  # 2. (non-continuous mode)
            "{}.expected_phase_{}".format(file_name, parsed_args.phase),  # 3. (non-continuous mode)
            "{}.expected".format(file_name),  # 4. (non-continuous mode)
        )
    else:
        expected_output_filenames = (
            "{}.expected_continuous_phase_{}".format(file_name, parsed_args.phase),  # 1. (continuous mode)
            "{}.expected_continuous".format(file_name),  # 2. (continuous mode)
        )
    for expected_output_filename in expected_output_filenames:
        if os.path.exists(expected_output_filename):
            with open(expected_output_filename, "r", encoding='utf-8') as myfile:
                return myfile.read().strip().splitlines()  # File exists, return the contents

    if parsed_args.cont_mode != "N":
        logger.info("No reference file '%s' in continuous mode - skipping test",
                    expected_output_filenames)  # 3. (continuous mode)
        sys.exit(0)

    raise FileNotFoundError("No reference file '{}'".format(expected_output_filenames))  # 4. (non-continuous mode)


def test():
    cmd_args = parse_command_line_args()
    dlinear_args = parse_dlinear_args(cmd_args)
    expected_output = get_expected_output(cmd_args)

    logger.debug("cmd_args: %s", cmd_args)
    logger.debug("dlinear_args: %s", dlinear_args)

    try:
        # 1. Run dReal with the input file
        out = subprocess.check_output([cmd_args.dlinear, cmd_args.file] + dlinear_args, env=dict(os.environ))
    except subprocess.CalledProcessError as e:
        logger.critical("error code %s %s", e.returncode, e.output)
        sys.exit(e.returncode)

    str_output = out.decode('UTF-8').splitlines()

    # 2. Compare the output with expected output
    diff_result = tuple(difflib.unified_diff(str_output,
                                             expected_output,
                                             fromfile='output',
                                             tofile='expected output',
                                             lineterm=''))
    if len(diff_result) > 0:
        # 3. They are not the same, show the diff.
        for line in diff_result:
            logger.error(line)
        sys.exit(1)

    # 4. They are the same.
    logger.debug("Test passed")
    sys.exit(0)


if __name__ == "__main__":
    test()
