# pylint: disable=missing-module-docstring,missing-function-docstring,missing-class-docstring,invalid-name
import csv
import re
from typing import TYPE_CHECKING
from .base_parser import BaseBenchmarkParser

if TYPE_CHECKING:
    from typing import TypedDict
    from base_parser import SloaneStufken, LPProblem, SMTProblem, TimeUnit

    class Benchmark(TypedDict):
        file: str
        solver: str
        assertions: int
        timeUnit: str
        time: int
        precision: float
        actualPrecision: float
        result: int


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
        solver = benchmark["solver"]
        result = "delta-sat" if int(benchmark["result"]) == 1 else "unsat"

        precision = float(benchmark["precision"])
        assertions = int(benchmark["assertions"])
        actual_precision = float(benchmark["actualPrecision"])
        time = self.time_conversion(benchmark["time"], benchmark["timeUnit"])

        key = f"{file}/{precision}"
        row: "LPProblem" = self.lp_problem_rows.get(
            key,
            {
                "file": file,
                "assertions": assertions,
                "precision": precision,
                "timeUnit": self.time_unit,
                "iterations": 1,
                "actualPrecisionS": -1,
                "actualPrecisionQ": -1,
                "timeS": -1,
                "timeQ": -1,
                "resultS": "/",
                "resultQ": "/",
            },
        )
        if solver == "soplex":
            row["actualPrecisionS"] = actual_precision
            row["timeS"] = round(time, 3)
            row["resultS"] = result
        elif solver == "qsoptex":
            row["actualPrecisionQ"] = actual_precision
            row["timeQ"] = round(time, 3)
            row["resultQ"] = result
        self.lp_problem_rows[key] = row

    def parse_sloane_stufken_problem(self, benchmark: "Benchmark"):
        file = benchmark["file"].split("/")[-1].removesuffix(".smt2")
        solver = benchmark["solver"]
        result = "delta-sat" if int(benchmark["result"]) == 1 else "unsat"

        precision = float(benchmark["precision"])
        assertions = int(benchmark["assertions"])
        actual_precision = float(benchmark["actualPrecision"])
        time = self.time_conversion(benchmark["time"], benchmark["timeUnit"])
        s1, k1, s2, k2, t = (int(val) for val in file.split("-"))

        key = f"{file}/{precision}"
        row: "SloaneStufken" = self.slone_stufken_rows.get(
            key,
            {
                "assertions": assertions,
                "precision": precision,
                "timeUnit": self.time_unit,
                "iterations": 1,
                "s1": s1,
                "k1": k1,
                "s2": s2,
                "k2": k2,
                "t": t,
                "actualPrecisionS": -1,
                "actualPrecisionQ": -1,
                "timeS": -1,
                "timeQ": -1,
                "resultS": "/",
                "resultQ": "/",
            },
        )
        if solver == "soplex":
            row["actualPrecisionS"] = actual_precision
            row["timeS"] = round(time, 3)
            row["resultS"] = result
        elif solver == "qsoptex":
            row["actualPrecisionQ"] = actual_precision
            row["timeQ"] = round(time, 3)
            row["resultQ"] = result
        self.slone_stufken_rows[key] = row

    def parse_smt_problem(self, benchmark: "Benchmark"):
        file = benchmark["file"].split("/")[-1].removeprefix("SMT_").removesuffix(".smt2")
        solver = benchmark["solver"]
        result = "delta-sat" if int(benchmark["result"]) == 1 else "unsat"

        precision = float(benchmark["precision"])
        assertions = int(benchmark["assertions"])
        actual_precision = float(benchmark["actualPrecision"])
        time = self.time_conversion(benchmark["time"], benchmark["timeUnit"])

        key = f"{file}/{precision}"
        row: "SMTProblem" = self.smt_problem_rows.get(
            key,
            {
                "file": file,
                "assertions": assertions,
                "precision": precision,
                "timeUnit": self.time_unit,
                "iterations": 1,
                "actualPrecisionS": -1,
                "actualPrecisionQ": -1,
                "timeS": -1,
                "timeQ": -1,
                "resultS": "/",
                "resultQ": "/",
            },
        )
        if solver == "soplex":
            row["actualPrecisionS"] = actual_precision
            row["timeS"] = round(time, 3)
            row["resultS"] = result
        elif solver == "qsoptex":
            row["actualPrecisionQ"] = actual_precision
            row["timeQ"] = round(time, 3)
            row["resultQ"] = result

    def _parse_benchmarks(self):
        for benchmark in self.benchmarks:
            file = benchmark["file"].split("/")[-1]
            if file.startswith("LP"):
                self.parse_lp_problem(benchmark)
            elif file.startswith("SMT"):
                self.parse_smt_problem(benchmark)
            elif file.endswith(".mps"):
                self.parse_lp_problem(benchmark)
            elif re.match(r"^(\d+-){4}\d+.smt2$", file):
                self.parse_sloane_stufken_problem(benchmark)
            else:
                self.parse_smt_problem(benchmark)
