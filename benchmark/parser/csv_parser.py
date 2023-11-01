# pylint: disable=missing-module-docstring,missing-function-docstring,missing-class-docstring,invalid-name
import csv
import re
from typing import TYPE_CHECKING
from .base_parser import BaseBenchmarkParser

if TYPE_CHECKING:
    from base_parser import SloaneStufken, LPProblem, SMTProblem, TimeUnit
    from .base_parser import Benchmark


class BenchmarkCsvParser(BaseBenchmarkParser):
    def __init__(
        self,
        input_files: "str | list[str]",
        output_file: "str",
        min_time: "int" = 0,
        time_unit: "TimeUnit" = "s",
    ):
        super().__init__(input_files, output_file, min_time, time_unit)
        assert all(input_file.endswith(".csv") for input_file in self.input_files)
        self.benchmarks: "list[Benchmark]" = []

    def load_benchmarks(self):
        self.benchmarks = []
        for input_file in self.input_files:
            with open(input_file, "r", encoding="utf-8") as f:
                reader = csv.DictReader(f)
                self.benchmarks += list(reader)  # type: ignore

    def parse_lp_problem(self, benchmark: "Benchmark"):
        file = benchmark["file"].split("/")[-1].removeprefix("LP_").removesuffix(".smt2").removesuffix(".mps")
        self.add_row(file, benchmark, self.lp_problem_rows)

    def parse_sloane_stufken_problem(self, benchmark: "Benchmark"):
        file = benchmark["file"].split("/")[-1].removeprefix("SMT_").removesuffix(".smt2")
        self.add_row(file, benchmark, self.slone_stufken_rows)

    def parse_smt_problem(self, benchmark: "Benchmark"):
        file = benchmark["file"].split("/")[-1].removeprefix("SMT_").removesuffix(".smt2")
        self.add_row(file, benchmark, self.smt_problem_rows)

    def _parse_benchmarks(self):
        for benchmark in self.benchmarks:
            file = benchmark["file"].split("/")[-1]
            if file.startswith("LP") or file.endswith(".mps"):
                self.parse_lp_problem(benchmark)
            elif file.startswith("SMT"):
                self.parse_smt_problem(benchmark)
            elif re.match(r"^(\d+-){4}\d+.smt2$", file):
                self.parse_sloane_stufken_problem(benchmark)
            else:
                self.parse_smt_problem(benchmark)
