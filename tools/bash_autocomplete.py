#!/usr/bin/env python3
import argparse
import shtab
from typing import TypedDict
import sys


class Completions(TypedDict):
    bash: str
    zsh: str


class Preamble:

    def __init__(self):
        self.extensions: dict[str, int] = {}
        self.files: list[Completions] = []
        self.preamble: Completions = {
            "bash": "",
            "zsh": "",
        }

    def file_by_extension(self, *extensions: "str"):
        extensions = tuple(ex.lower() for ex in extensions)
        if extensions in self.extensions:
            return self.files[self.extensions[extensions]]

        zsh_compgen = [f"*.{extension}|*.{extension.upper()}" for extension in extensions]
        zsh_compgen = "|".join(zsh_compgen)
        self.files.append(
            {
                "bash": f"_shtab_pydlinear_compgen_{'_'.join(extensions)}_files",
                "zsh": f"_files -g '({zsh_compgen})'",
            }
        )
        bash_compgen = [
            f"compgen -f -X '!*?.{extension}' -- $1\ncompgen -f -X '!*?.{extension.upper()}' -- $1"
            for extension in extensions
        ]
        bash_compgen = "\n".join(bash_compgen)
        self.preamble[
            "bash"
        ] += f"""
_shtab_pydlinear_compgen_{'_'.join(extensions)}_files() {{
  compgen -d -- $1  # recurse into subdirs
  {bash_compgen}
}}

"""
        self.extensions[extensions] = len(self.files) - 1
        return self.files[-1]

    @property
    def bash_preamble(self):
        return self.preamble["bash"]


def get_parser(prog: str, preamble: Preamble):
    parser = argparse.ArgumentParser(prog=prog)
    # file & directory tab complete
    parser.add_argument("file", type=argparse.FileType("r")).complete = preamble.file_by_extension(
        "smt2", "mps", "vnnlib"
    )
    parser.add_argument("--onnx-file", type=argparse.FileType("r")).complete = preamble.file_by_extension("onnx")
    # Flags
    parser.add_argument("--csv", action="store_true")
    parser.add_argument("--continuous-output", action="store_true")
    parser.add_argument("-c", "--complete", action="store_true")
    parser.add_argument("--debug-parsing", action="store_true")
    parser.add_argument("--debug-scanning", action="store_true")
    parser.add_argument("--disable-expansion", action="store_true")
    parser.add_argument("--enforce-check-sat", action="store_true")
    parser.add_argument("-o", "--optimize", action="store_true")
    parser.add_argument("-m", "--produce-models", action="store_true")
    parser.add_argument("--skip-check-sat", action="store_true")
    parser.add_argument("-s", "--silent", action="store_true")
    parser.add_argument("-t", "--timings", action="store_true")
    parser.add_argument("--in", action="store_true")
    parser.add_argument("--verify", action="store_true")
    parser.add_argument("-v", "--version", action="store_true")
    parser.add_argument("-V", action="store_true")
    parser.add_argument("-q", action="store_true")

    # Values
    parser.add_argument("-p", "--precision", type=float)
    parser.add_argument("-r", "--random-seed", type=int)
    parser.add_argument("--simplex-sat-phase", type=int)
    parser.add_argument("--verbose-simplex", type=int)

    # Choices
    parser.add_argument("--lp-mode", choices=["auto", "pure-precision-boosting", "pure-iterative-refinement", "hybrid"])
    parser.add_argument("--format", choices=["auto", "smt2", "mps", "vnnlib"])
    parser.add_argument("--lp-solver", choices=["soplex", "qsoptex"])
    parser.add_argument("--sat-solver", choices=["cadical", "picosat"])
    parser.add_argument("--sat-default-phase", choices=["false", "true", "jeroslow-wang", "random"])
    parser.add_argument(
        "--bound-propagation-type", choices=["auto", "eq-binomial", "eq-polynomial", "bound-polynomial"]
    )
    parser.add_argument(
        "--bound-propagation-frequency", choices=["auto", "never", "on-fixed", "on-iteration", "always"]
    )
    parser.add_argument("--bound-implication-frequency", choices=["auto", "never", "always"])

    return parser


def complete_bash(prog: str, output: str):
    preamble = Preamble()
    autocomplete_script = shtab.complete_bash(get_parser(prog, preamble), preamble=preamble.bash_preamble)
    with open(output, "w", encoding="utf-8") as f:
        f.write(autocomplete_script)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        print(f"usage: {sys.argv[0]} <dlinear|dlinear> <out_file.sh>")
        exit(1)
    complete_bash(sys.argv[1], sys.argv[2])
