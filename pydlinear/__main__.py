import pydlinear as pdl
import sys


def main():
    config = pdl.Config.from_command_line(sys.argv)
    config.lp_solver = pdl.LPSolver.SOPLEX
    pdl.init_solver(config)
    pdl.Smt2Driver(config).parse_file()


if __name__ == "__main__":
    main()
