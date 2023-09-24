import pydlinear as pdl
import sys


config = pdl.Config.from_command_line(sys.argv)
with pdl.Solver(config) as s:
    print(s.CheckSat())
