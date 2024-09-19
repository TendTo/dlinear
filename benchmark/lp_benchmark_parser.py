#!/usr/bin/python3
import os
import csv
from typing import TYPE_CHECKING
from abc import abstractmethod, ABC
import glob
import re
import sys

if TYPE_CHECKING:
    from typing import Literal, Iterable

TIME_UNITS = ["ns", "us", "ms", "s", "m", "h"]
TIME_UNITS_TRANSITIONS = [
    [1, 1e-3, 1e-6, 1e-9, 1e-9 / 60, 1e-9 / 3600],
    [1e3, 1, 1e-3, 1e-6, 1e-6 / 60, 1e-6 / 3600],
    [1e6, 1e3, 1, 1e-3, 1e-3 / 60, 1e-3 / 3600],
    [1e9, 1e6, 1e3, 1, 1 / 60, 1 / 3600],
    [1e9 * 60, 1e6 * 60, 1e3 * 60, 60, 1, 1 / 60],
    [1e9 * 3600, 1e6 * 3600, 1e3 * 3600, 3600, 60, 1],
]


class BaseInstance(ABC):
    def __init__(self, expected_file: str, dir_path: str):
        self._expected_file = expected_file
        self._dir_path = dir_path
        self._filename = os.path.basename(self.smt2_filename_to_mps(expected_file))
        self._time = -1
        self._result = ""

    @classmethod
    @abstractmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D']":
        pass

    @classmethod
    @abstractmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear']":
        pass

    @classmethod
    @abstractmethod
    def file_ext(cls) -> "Literal['.cvc5.expected', '.z3.expected', '.yices.expected']":
        pass

    @abstractmethod
    def smt2_filename_to_mps(self, smt2: str) -> str:
        return smt2.replace("LP_", "").replace(".smt2", "") + ".mps"

    @abstractmethod
    def get_filename(self, content: "str | None" = None) -> str:
        pass

    @abstractmethod
    def get_time(self, content: "str | None" = None) -> float:
        pass

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat']":
        pass

    def parse_stats(self):
        with open(self._expected_file, "r", encoding="utf-8") as f:
            expected_str = f.read()
        if len(expected_str.strip()) == 0:
            return
        self._filename = self._filename or self.smt2_filename_to_mps(self.get_filename(expected_str))
        self._time = self._time if self._time != -1 else self.get_time(expected_str)
        self._result = self._result or self.get_result(expected_str)

    @property
    def parsed(self):
        print(f"time: {self._time} file: {self._filename} res: {self._result}")
        return self._time != -1 and self._filename != "" and self._result in ("sat", "unsat")

    @property
    def results(self) -> "dict[str, str | float]":
        return {
            "file": self._filename,
            f"time{self.solver_id()}": self._time,
            f"result{self.solver_id()}": self._result,
        }

    @classmethod
    def store_csv(cls, instances: "Iterable[BaseInstance]"):
        print(f"Read {len(instances)} lines")
        parsed_results = tuple(map(lambda instance: instance.results, filter(lambda x: x.parsed, instances)))

        print(f"Storing {len(parsed_results)} lines")
        if len(parsed_results) == 0:
            return
        return
        with open(f"{cls.solver()}_lp.csv", "w", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=parsed_results[0].keys())
            writer.writeheader()
            writer.writerows(parsed_results)

    @classmethod
    def parse_and_store(cls, dir_path: str):
        ext = cls.file_ext()
        files = glob.glob(f"{dir_path}/*{ext}")
        instances = [cls(file, dir_path) for file in files]
        for instance in instances:
            instance.parse_stats()
        cls.store_csv(instances)


class Z3Instance(BaseInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D']":
        return "Z"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear']":
        return "z3"

    @classmethod
    def file_ext(cls) -> "Literal['.cvc5.expected', '.z3.expected', '.yices.expected']":
        return ".z3.expected"

    def get_filename(self, content: "str | None" = None) -> str:
        raise RuntimeError("No filename detected")

    def get_time(self, content: "str | None" = None) -> float:
        matches = re.findall(r" *:total-time *(.+)\)", content)
        if len(matches) == 1:
            return float(matches[0])
        return -1

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat']":
        return content.splitlines()[0]

    def smt2_filename_to_mps(self, smt2: str) -> str:
        return super().smt2_filename_to_mps(smt2.replace(".z3.expected", ".smt2"))


class Cvc5Instance(BaseInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D']":
        return "C"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear']":
        return "cvc5"

    @classmethod
    def file_ext(cls) -> "Literal['.cvc5.expected', '.z3.expected', '.yices.expected']":
        return ".cvc5.expected"

    def get_filename(self, content: "str | None" = None) -> str:
        stats_file = self._expected_file.replace(".expected", ".stats")
        with open(stats_file, "r", encoding="utf-8") as f:
            stats_content = f.read()
        matches = re.findall(r"filename *= *(.+)", stats_content)
        for m in matches:
            return m
        return ""

    def get_time(self, content: "str | None" = None) -> float:
        stats_file = self._expected_file.replace(".expected", ".stats")
        with open(stats_file, "r", encoding="utf-8") as f:
            stats_content = f.read()
        matches = re.findall(r"totalTime *= *(\d+)(\w+)", stats_content)
        for m in matches:
            if len(m) == 2:
                return int(m[0]) * TIME_UNITS_TRANSITIONS[TIME_UNITS.index(m[1])][TIME_UNITS.index("s")]
        return -1

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat']":
        return content.strip()

    def smt2_filename_to_mps(self, smt2: str) -> str:
        return super().smt2_filename_to_mps(smt2.replace(".cvc5.expected", ".smt2"))


class YicesInstance(BaseInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D']":
        return "Y"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear']":
        return "yices"

    @classmethod
    def file_ext(cls) -> "Literal['.cvc5.expected', '.z3.expected', '.yices.expected']":
        return ".yices.expected"

    def get_filename(self, content: "str | None" = None) -> str:
        raise RuntimeError("No filename detected")

    def get_time(self, content: "str | None" = None) -> float:
        matches = re.findall(r" *:total-run-time (.+)", content)
        if len(matches) == 1:
            return float(matches[0])
        return -1

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat']":
        return content.splitlines()[0]

    def smt2_filename_to_mps(self, smt2: str) -> str:
        return super().smt2_filename_to_mps(smt2.replace(".yices.expected", ".smt2"))


def main(solver: "Literal['cvc5', 'z3', 'yices']" = "no-solver-selected", dir_path: str = "lp_results"):
    if solver == "cvc5":
        Cvc5Instance.parse_and_store(dir_path)
    elif solver == "z3":
        Z3Instance.parse_and_store(dir_path)
    elif solver == "yices":
        YicesInstance.parse_and_store(dir_path)
    else:
        raise ValueError(f"Unknown solver: {solver}")


if __name__ == "__main__":
    main(*sys.argv[1:])
