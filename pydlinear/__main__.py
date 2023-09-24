import sys
import pydlinear as pdl


def main():
    config = pdl.Config.from_command_line(sys.argv)
    with pdl.Solver(config) as s:
        print(s.CheckSat())


if __name__ == "__main__":
    main()
