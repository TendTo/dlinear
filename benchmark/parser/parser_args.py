import os
import argparse


def parse_command_line_args() -> "argparse.Namespace":
    def file(filename: "str") -> "str":
        if not os.path.exists(filename):
            raise argparse.ArgumentTypeError(f"{filename} does not exist")
        return filename

    parser = argparse.ArgumentParser(
        description="Parse the results from the dlinear benchmarking software and output a compact csv."
    )
    parser.add_argument(
        "input_files", type=file, nargs="+", help="input file to parse. Should be either a .csv or a .json file"
    )
    parser.add_argument("output_file", type=str, help="output file to write. Will be a .csv file")
    parser.add_argument(
        "-m", "--min-time", type=int, help="minimum time to consider. If 0, consider all times", default=0
    )

    args = parser.parse_args()
    return args
