#!/usr/bin/python3
import os
import csv
from typing import TYPE_CHECKING
from abc import abstractmethod, ABC
import glob
import re
import sys
import argparse

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
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        pass

    @classmethod
    @abstractmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        pass

    @classmethod
    def file_ext(cls) -> "Literal['.cvc5.expected', '.z3.expected', '.yices.expected']":
        return f".{cls.solver()}.expected"

    def smt2_filename_to_mps(self, smt2: str) -> str:
        smt2 = smt2.replace(self.file_ext(), ".smt2")
        if smt2.startswith("LP_"):
            return smt2.replace("LP_", "", 1).replace(".smt2", ".mps", 1)
        return smt2

    @abstractmethod
    def get_filename(self, content: "str | None" = None) -> str:
        pass

    @abstractmethod
    def get_time(self, content: "str | None" = None) -> float:
        pass

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat', 'unknown', 'timeout']":
        pass

    def parse_stats(self):
        with open(self._expected_file, "r", encoding="utf-8") as f:
            expected_str = f.read()
        if len(expected_str.strip()) == 0:
            return
        self._filename = self._filename or self.smt2_filename_to_mps(self.get_filename(expected_str))
        self._time = self._time if self._time != -1 else self.get_time(expected_str)
        self._result = self._result or self.get_result(expected_str)

    @classmethod
    def get_output_filename(cls) -> str:
        return f"{cls.solver()}.csv"

    @property
    def parsed(self):
        return self._time != -1 and self._filename != "" and self._result in ("sat", "unsat", "unknown", "timeout")

    @property
    def results(self) -> "dict[str, str | float]":
        return {
            "file": self._filename,
            f"time{self.solver_id()}": self._time,
            f"result{self.solver_id()}": self._result,
        }

    def __str__(self) -> str:
        return f"{self.solver()}(filename={self._filename}, time={self._time}, result={self._result})"

    @classmethod
    def override_keys(cls) -> "Iterable[str]":
        return tuple()

    @classmethod
    def store_csv(cls, instances: "Iterable[BaseInstance]", args: "argparse.Namespace | None" = None):
        print(f"Read {len(instances)} lines")
        parsed_results = tuple(map(lambda instance: instance.results, filter(lambda x: x.parsed, instances)))
        failed = tuple(map(lambda instance: instance.results, filter(lambda x: not x.parsed, instances)))
        if args is not None and args.verbose:
            for f in failed:
                print(f"Failed to parse: {f}", file=sys.stderr)

        print(f"Storing {len(parsed_results)} lines, failed to parse {len(failed)} lines")
        if len(parsed_results) == 0:
            return
        if not os.path.exists(args.output_dir):
            os.makedirs(args.output_dir)
        with open(f"{args.output_dir}/{cls.get_output_filename()}", "w", encoding="utf-8") as f:
            writer = csv.DictWriter(f, fieldnames=cls.override_keys() or tuple(parsed_results[0].keys()))
            writer.writeheader()
            writer.writerows(parsed_results)

    @classmethod
    def parse_and_store(cls, args: argparse.Namespace):
        dir_path = args.directory
        ext = cls.file_ext()
        files = glob.glob(f"{dir_path}/*{ext}")
        instances = [cls(file, dir_path) for file in files]
        for instance in instances:
            instance.parse_stats()
        cls.store_csv(instances, args)


class Z3Instance(BaseInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        return "Z"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        return "z3"

    def get_filename(self, content: "str | None" = None) -> str:
        raise RuntimeError("No filename detected")

    def get_time(self, content: "str | None" = None) -> float:
        matches = re.findall(r" *:total-time *(.+)\)", content)
        if len(matches) == 1:
            return float(matches[0])
        return -1

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat', 'unknown', 'timeout']":
        return content.splitlines()[0]


class Cvc5Instance(BaseInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        return "C"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        return "cvc5"

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

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat', 'unknown', 'timeout']":
        return content.strip()


class YicesInstance(BaseInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        return "Y"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        return "yices"

    def get_filename(self, content: "str | None" = None) -> str:
        raise RuntimeError("No filename detected")

    def get_time(self, content: "str | None" = None) -> float:
        matches = re.findall(r" *:total-run-time (.+)", content)
        if len(matches) == 1:
            return float(matches[0])
        return -1

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat', 'unknown', 'timeout']":
        return content.splitlines()[0]


class Cvc5ExternalInstance(BaseInstance):
    iterations = -1
    strict = False
    delta = -1
    values_keys = []
    captured_stats = (
        "options::pivots",
        "options::checkModels",
        "options::strict",
        "options::delta",
        "options::external-lp-solver",
        "theory::arith::z::approx::externalAdjustmentPivots",
        "theory::arith::z::approx::delta",
        "theory::arith::z::approx::deltaResults",
        "theory::arith::z::approx::strictVar",
        "theory::arith::z::arith::relax::calls",
        "theory::arith::z::arith::relax::exhausted",
        "theory::arith::z::arith::relax::feasible::failures",
        "theory::arith::z::arith::relax::feasible::res",
        "theory::arith::z::arith::relax::infeasible",
        "theory::arith::z::arith::relax::infeasible::failures",
        "theory::arith::z::arith::relax::other",
        "theory::arith::z::approx::lp::timer ",
        "theory::arith::z::approx::lp::setup::timer ",
        "theory::arith::z::approx::pivotLimit",
        "theory::arith::z::approx::externalSimplexType",
        "theory::arith::z::approx::precision",
        "theory::arith::z::approx::refinements",
        "theory::arith::pivots",
        "TheoryEngine::Checks_Full",
        "TheoryEngine::Checks_Last_Call",
        "TheoryEngine::Checks_Standard",
        "TheoryEngine::combineTheoriesCalls",
        "TheoryEngine::combineTheoriesTime",
        "driver::filename",
        "global::totalTime",
        "preprocessing::theory-preprocess",
        "sat::clauses_literals",
        "sat::conflicts",
        "sat::decisions",
        "sat::learnts_literals",
        "sat::max_literals",
        "sat::propagations",
        "sat::rnd_decisions",
        "sat::starts",
        "sat::tot_literals",
        "theory::arith::AssertLowerConflicts",
        "theory::arith::AssertUpperConflicts",
        "theory::arith::AuxiliaryVariables",
        "theory::arith::DisequalityConflicts",
        "theory::arith::DisequalitySplits",
        "theory::arith::UserVariables",
        "theory::arith::attempt::conflicts",
        "theory::arith::attempt::queueTime",
        "theory::arith::attempt::searchTime",
        "theory::arith::attempt::extendedSearch",
        "theory::arith::checkTime",
        "theory::arith::conflicts",
        "theory::arith::pivots",
        "theory::arith::status::nontrivialSatChecks",
        "theory::arith::updates",
    )

    def __init__(self, expected_file: str, dir_path: str):
        super().__init__(expected_file, dir_path)
        self.values: dict[str, str | float] = {}

    def get_filename(self, content: "str | None" = None) -> str:
        raise RuntimeError("No filename detected")

    def get_time(self, content: "str | None" = None) -> float:
        stats_file = self._expected_file.replace(".expected", ".stats")
        with open(stats_file, "r", encoding="utf-8") as f:
            stats_content = f.read()
            self.parse_vals(stats_content)
        matches = re.findall(r"(\d+)(\w+)", self.values.get("global::totalTime", ""))
        for m in matches:
            if len(m) == 2:
                return int(m[0]) * TIME_UNITS_TRANSITIONS[TIME_UNITS.index(m[1])][TIME_UNITS.index("s")]
        return -1

    def get_result(self, content: "str | None" = None) -> "Literal['sat', 'unsat', 'unknown', 'timeout']":
        lines = content.splitlines() if content is not None else []
        return lines[-1].strip()

    def parse_vals(self, content: "str | None" = None):
        lines = content.splitlines() if content is not None else []
        for line in lines:
            for stat in self.captured_stats:
                if line.lower().startswith(stat.lower()):
                    key, val = line.split(" = ")
                    if key not in self.values:
                        self.values[key] = val.strip()
                        self.__class__.iterations = (
                            int(val.strip()) if stat == "options::pivots" else self.__class__.iterations
                        )
                        self.__class__.strict = (val.strip() == "1" if stat == "options::strict" else self.__class__.strict)
                        self.__class__.delta = (float(val.strip()) if stat == "options::delta" else self.__class__.delta)
                    break
        if len(self.values) > len(self.__class__.values_keys):
            self.__class__.values_keys = list(self.values.keys())

    @classmethod
    def override_keys(cls) -> "Iterable[str]":
        return cls.values_keys + [f"result{cls.solver_id()}", f"time{cls.solver_id()}", "file"]

    @property
    def results(self) -> "dict[str, str | float]":
        return self.values | {
            "file": self._filename,
            f"time{self.solver_id()}": self._time,
            f"result{self.solver_id()}": self._result,
        }

    @classmethod
    def get_output_filename(cls) -> str:
        iterations = f"_i{cls.iterations}" if cls.iterations != -1 else ""
        strict = "_strict" if cls.solver() in ("soplex", "qsoptex") and cls.strict else ""
        delta = f"_delta{cls.delta}" if cls.delta >= 0 else ""
        return f"{cls.solver()}{iterations}{strict}{delta}.csv"


class SoplexInstance(Cvc5ExternalInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        return "S"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        return "soplex"


class GlpkInstance(Cvc5ExternalInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        return "G"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        return "glpk"


class QsoptexInstance(Cvc5ExternalInstance):
    @classmethod
    def solver_id(cls) -> "Literal['C', 'Z', 'Y', 'D', 'S', 'G', 'Q']":
        return "Q"

    @classmethod
    def solver(cls) -> "Literal['cvc5', 'z3', 'yices', 'dlinear', 'soplex', 'glpk', 'qsoptex']":
        return "qsoptex"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Parse solver results and store them in CSV files.")
    parser.add_argument(
        "solver",
        choices=["cvc5", "z3", "yices", "dlinear", "soplex", "glpk", "qsoptex"],
        help="The solver whose results to parse.",
    )
    parser.add_argument("directory", help="The directory containing the .expected files to parse.")
    parser.add_argument("--output-dir", "-o", default=".", help="The directory to store the output CSV files (default: current directory).")
    parser.add_argument("--verbose", "-V", action="store_true", help="Print verbose output.")
    return parser.parse_args()


def main():
    args = parse_args()
    solver = args.solver
    if solver == "cvc5":
        Cvc5Instance.parse_and_store(args)
    elif solver == "z3":
        Z3Instance.parse_and_store(args)
    elif solver == "yices":
        YicesInstance.parse_and_store(args)
    elif solver == "soplex":
        SoplexInstance.parse_and_store(args)
    elif solver == "glpk":
        GlpkInstance.parse_and_store(args)
    elif solver == "qsoptex":
        QsoptexInstance.parse_and_store(args)
    else:
        raise ValueError(f"Unknown solver: {solver}")


if __name__ == "__main__":
    main()
