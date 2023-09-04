import pydlinear as p

c = p.Config() # Uses the default options
# Initializes the correct solver for the configuration
p.init_solver(c)

d = p.Smt2Driver(c)
d.parse_file("input.smt2") # Run the "input.smt2" file
