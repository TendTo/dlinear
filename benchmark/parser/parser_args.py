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
    parser.add_argument(
        "-u",
        "--time-unit",
        type=str,
        help="time unit to use. The time results will be converted in this time unit. Default is s",
        default="s",
        choices=["ns", "us", "ms", "s", "m", "h"],
    )

    args = parser.parse_args()
    return args
