#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Run dlinear on a smt2 file. Compare the results against a reference.
By default, the reference is the .expected file in the same directory as the smt2 file.

The name of the output file is built using the following rules in order:

- If the solver is not in continuous mode:
    1. The same name of the smt2 file with the extension .%solver.expected
        (e.g. smt2/input.smt2 -> smt2/input.smt2.soplex.expected)
    2. The same name of the smt2 file with the extension .expected
        (e.g. smt2/input.smt2 -> smt2/input.smt2.expected)
    3. The same name of the smt2 file with the extension .expected_phase_%n
        (e.g. smt2/input.smt2 -> smt2/input.smt2.expected_phase_1 for phase 1)
        (e.g. smt2/input.smt2 -> smt2/input.smt2.expected_phase_2 for phase 2)
    4. Raise an error if no reference file is found
- If the solver is in continuous mode:
    1. The same name of the smt2 file with the extension .expected_continuous
        (e.g. smt2/input.smt2 -> smt2/input.smt2.expected_continuous)
    2. The same name of the smt2 file with the extension .expected_continuous_phase_%n
        (e.g. smt2/input.smt2 -> smt2/input.smt2.expected_continuous_phase_1 for phase 1)
        (e.g. smt2/input.smt2 -> smt2/input.smt2.expected_continuous_phase_2 for phase 2)
    3. Skip the test if no reference file is found

Usage: TestSmt2.py dlinear smt2 lp_solver phase cont_mode [options]

Example: TestSmt2.py ./dlinear smt2/input.smt2 qsoptex 1 False N
The above command will run dlinear on the smt2 file with qsoptex, phase 1, SoPlex disabled, and no continuous mode.
The output will be compared against smt2/input.smt2.expected
"""
import sys
import os
import subprocess
import difflib
import argparse
import logging
from util.args import parse_command_line_args

logging.basicConfig(level=logging.DEBUG, format="%(asctime)s %(levelname)s %(message)s")
logger = logging.getLogger(__name__)

if __name__ == "__main__":
    args = parse_command_line_args()
    print(args)
