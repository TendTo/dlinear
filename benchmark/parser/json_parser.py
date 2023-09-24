# pylint: disable=missing-module-docstring,missing-function-docstring,missing-class-docstring,invalid-name
import json
import re
from typing import TYPE_CHECKING
from .base_parser import BaseBenchmarkParser

if TYPE_CHECKING:
    from typing import TypedDict
    from base_parser import SloaneStufken, LPProblem, SMTProblem, TimeUnit

    class Benchmark(TypedDict):
        name: str
        family_index: int
        per_family_instance_index: int
        run_name: str
        run_type: str
        repetitions: int
        repetition_index: int
        threads: int
        iterations: int
        real_time: float
        cpu_time: float
        time_unit: str


class BenchmarkJsonParser(BaseBenchmarkParser):
    def __init__(
        self,
        input_file: "str | list[str]",
        output_file: "str",
        min_time: "int" = 0,
        time_unit: "TimeUnit" = "s",
    ):
        super().__init__(input_file, output_file, min_time, time_unit)
        assert all(input_file.endswith(".json") for input_file in self.input_files)
        self.benchmarks: "list[Benchmark]" = []

    def load_benchmarks(self):
        self.benchmarks = []
        for input_file in self.input_files:
            with open(input_file, "r", encoding="utf-8") as f:
                benchmark_json: "dict" = json.load(f)
                self.benchmarks += benchmark_json.get("benchmarks", [])

    def parse_lp_problem(self, benchmark: "Benchmark"):
        file, solver, precision, actual_precision, assertions, result = benchmark["name"].split(",")

        file = file.split("/")[-1]
        file = file.removeprefix("LP_")
        file = file.removesuffix(".smt2")
        precision = float(precision)
        assertions = int(assertions)
        actual_precision = float(actual_precision)
        time = self.time_conversion(benchmark["cpu_time"], benchmark["time_unit"])

        key = f"{file}/{precision}"
        row: "LPProblem" = self.lp_problem_rows.get(
            key,
            {
                "file": file,
                "assertions": assertions,
                "precision": precision,
                "timeUnit": self.time_unit,
                "iterations": benchmark["iterations"],
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
        file, solver, precision, actual_precision, assertions, result = benchmark["name"].split(",")

        file = file.split("/")[-1]
        file = file.removesuffix(".smt2")
        precision = float(precision)
        assertions = int(assertions)
        actual_precision = float(actual_precision)
        s1, k1, s2, k2, t = (int(val) for val in file.split("-"))
        time = self.time_conversion(benchmark["cpu_time"], benchmark["time_unit"])

        key = f"{file}/{precision}"
        row: "SloaneStufken" = self.slone_stufken_rows.get(
            key,
            {
                "assertions": assertions,
                "precision": precision,
                "timeUnit": self.time_unit,
                "iterations": benchmark["iterations"],
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
        file, solver, precision, actual_precision, assertions, result = benchmark["name"].split(",")

        file = file.split("/")[-1]
        file = file.removesuffix(".smt2")
        file = file.removeprefix("SMT_")
        precision = float(precision)
        assertions = int(assertions)
        actual_precision = float(actual_precision)
        time = self.time_conversion(benchmark["cpu_time"], benchmark["time_unit"])

        key = f"{file}/{precision}"
        row: "SMTProblem" = self.smt_problem_rows.get(
            key,
            {
                "file": file,
                "assertions": assertions,
                "precision": precision,
                "timeUnit": self.time_unit,
                "iterations": benchmark["iterations"],
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
        self.smt_problem_rows[key] = row

    def _parse_benchmarks(self):
        for benchmark in self.benchmarks:
            file = benchmark["name"].split(",")[0]
            file = file.split("/")[-1]
            if file.startswith("LP"):
                self.parse_lp_problem(benchmark)
            elif file.startswith("SMT"):
                self.parse_smt_problem(benchmark)
            elif re.match(r"^(\d+-){4}\d+.smt2$", file):
                self.parse_sloane_stufken_problem(benchmark)
            else:
                self.parse_smt_problem(benchmark)
