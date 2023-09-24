#!/usr/bin/env python3
# pylint: disable=missing-module-docstring,missing-function-docstring,missing-class-docstring,invalid-name
from parser.csv_parser import BenchmarkCsvParser
from parser.parser_args import parse_command_line_args


def main():
    args = parse_command_line_args()

    benchmark_parser = BenchmarkCsvParser(
        args.input_files, args.output_file, args.min_time, time_unit=args.time_unit
    )
    benchmark_parser.parse_benchmarks()


if __name__ == "__main__":
    main()
