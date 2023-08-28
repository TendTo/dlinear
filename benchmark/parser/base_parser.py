# pylint: disable=missing-module-docstring,missing-function-docstring,missing-class-docstring,invalid-name
import csv
from typing import TYPE_CHECKING
import os
from abc import ABC, abstractmethod

if TYPE_CHECKING:
    from typing import TypedDict, Literal

    TimeUnit = Literal["ns", "us", "ms", "s", "m", "h"]

    class SloaneStufken(TypedDict):
        assertions: int
        precision: float
        timeUnit: str
        iterations: int
        s1: int
        k1: int
        s2: int
        k2: int
        t: int
        actualPrecisionS: float
        actualPrecisionQ: float
        timeS: float
        timeQ: float
        resultS: str
        resultQ: str

    class LPProblem(TypedDict):
        file: str
        assertions: int
        precision: float
        timeUnit: str
        iterations: int
        actualPrecisionS: float
        actualPrecisionQ: float
        timeS: float
        timeQ: float
        resultS: str
        resultQ: str

    class SMTProblem(TypedDict):
        file: str
        assertions: int
        precision: float
        timeUnit: str
        iterations: int
        actualPrecisionS: float
        actualPrecisionQ: float
        timeS: float
        timeQ: float
        resultS: str
        resultQ: str


class BaseBenchmarkParser(ABC):
    TIME_UNITS = ["ns", "us", "ms", "s", "m", "h"]
    TIME_UNITS_TRANSITIONS = [
        [1, 1e-3, 1e-6, 1e-9, 1e-9 / 60, 1e-9 / 3600],
        [1e3, 1, 1e-3, 1e-6, 1e-6 / 60, 1e-6 / 3600],
        [1e6, 1e3, 1, 1e-3, 1e-3 / 60, 1e-3 / 3600],
        [1e9, 1e6, 1e3, 1, 1 / 60, 1 / 3600],
        [1e9 * 60, 1e6 * 60, 1e3 * 60, 60, 1, 1 / 60],
        [1e9 * 3600, 1e6 * 3600, 1e3 * 3600, 3600, 60, 1],
    ]

    def __init__(
        self,
        input_files: "str | list[str]",
        output_file: "str",
        smt2_folder: "str" = "",
        min_time: int = 0,
        time_unit: "TimeUnit" = "s",
    ) -> None:
        self.input_files: "list[str]" = input_files if isinstance(input_files, list) else [input_files]
        self.output_file: "str" = output_file
        self.smt2_folder: "str" = smt2_folder
        self.lp_problem_rows: "dict[str, LPProblem]" = {}
        self.slone_stufken_rows: "dict[str, SloaneStufken]" = {}
        self.smt_problem_rows: "dict[str, SMTProblem]" = {}
        self.min_time: "int" = min_time
        self.time_unit: "TimeUnit" = time_unit

    @abstractmethod
    def load_benchmarks(self):
        pass

    def write_benchmarks_csv(self):
        self.write_cvs("lp")
        self.write_cvs("ss")
        self.write_cvs("smt")

    def write_cvs(self, row_type: "Literal['ss', 'smt', 'lp']"):
        file_row = self.lp_problem_rows
        match row_type:
            case "ss":
                file_row = self.slone_stufken_rows
            case "smt":
                file_row = self.smt_problem_rows
            case "lp":
                file_row = self.lp_problem_rows

        rows = [file_row for file_row in file_row.values() if self.should_add_row(file_row)]

        if len(rows) == 0:
            return

        with open(self.get_output_file_with_prefix(row_type), "w", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=rows[0].keys())
            writer.writeheader()
            writer.writerows(rows)

    @abstractmethod
    def parse_lp_problem(self, benchmark):
        pass

    @abstractmethod
    def parse_sloane_stufken_problem(self, benchmark):
        pass

    @abstractmethod
    def parse_smt_problem(self, benchmark):
        pass

    @abstractmethod
    def _parse_benchmarks(self):
        pass

    def parse_benchmarks(self):
        self.load_benchmarks()

        self._parse_benchmarks()

        self.write_benchmarks_csv()

    def get_output_file_with_prefix(self, prefix: "str") -> "str":
        filename = f"{prefix}{os.path.basename(self.output_file)}"
        return os.path.join(os.path.dirname(self.output_file), filename)

    def should_add_row(self, benchmark: "SloaneStufken | LPProblem | SMTProblem") -> "bool":
        return self.min_time == 0 or benchmark["timeQ"] >= self.min_time or benchmark["timeS"] >= self.min_time

    def time_conversion(self, time: "float | str", time_unit: "TimeUnit | str") -> "float":
        if isinstance(time, str):
            time = float(time)
        if time_unit not in self.TIME_UNITS or self.time_unit not in self.TIME_UNITS:
            raise ValueError(f"Unknown time unit {time_unit}")

        from_unit = self.TIME_UNITS.index(time_unit)
        to_unit = self.TIME_UNITS.index(self.time_unit)

        scale = self.TIME_UNITS_TRANSITIONS[from_unit][to_unit]
        return time * scale
