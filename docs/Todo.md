# TODO

## Software

- [x] Fix qsoptex Farkas ray
    - [x] Relegate qsoptex to compilation flag
- [x] Make sure the solution match between the two test_solvers
- [x] Check what happens by removing `Expand` from `Formula`
    - It can be done only for mps files, since the structure of the formula is not always plain otherwise
- [x] Add inequality support
- [ ] Clean up benchmarking suite
- [x] Clean up `pydlinear`
- [x] Remove unused Config parameters
- [x] Improve nolog options
- [x] Make the sat return type a struct
- [x] Separate smt time between sat and theory
- [x] Sort bounds by value so that it is possible to invalidate just the ones on one side
    - [x] Sorted container for the bounds
    - [x] Find the value of the violated bound for infeasible problems
- [x] Store the value for each bit of the bit iterator and re-use it for next iterations
- [ ] Optimise situations where multiple nq constraints are violated at the same time
- [ ] Linked variables for bound checking
- [x] Multiple explanations for invalid bounds
- [x] Heuristics options
- [x] In the presence of eq bounds, they should be the only one returned by the active_bounds() method
- [x] Optimal explanation when all nq constraints combination have been explored
- [ ] Include a starting iterator when searching lower and upper bounds, so that the search can be resumed from the last
  point
- [x] Reduce the number of copies of inf and ninf bounds in the bound vector
- [ ] Use c++20 format instead of the external library
    - [ ] Use Ubuntu 23.04+ for gcc 13+ support
- [ ] Return multiple explanations instead of just one when dealing with active constraints
- [ ] Improve iterations over nq bounds
- [x] Add symbolic preprocessor for constraints in the form of $x \lessgtr y$
- [ ] Remove completely free variables, especially from nq constraints
- [ ] Investigate out of memory
- [x] Handle conflicting constraints in preprocessor
- [x] Fix Invalidly reported constraints in bound processor
- [x] Add support for `max` and `min` functions redefinitions
- [x] Update `smt2` parser
- [x] Use lazy cache for Formula's GetFreeVariables
- [ ] Custom symbolic implementation
- [ ] Report need for basis reset in Soplex (a bug in the solver?)
- [x] Use the information from the preprocessor to guide the theory solver. Make sure the graph or causality is
  respected
- [x] Remove Infinity singleton
- [ ] Support string problem input
- [x] Avoid resetting all constraints in the theory solver at each iteration. Instead, reset only the ones that have
  been removed and add or update the new ones
- [ ] NN verification benchmarks
- [ ] Add support for integer variables
- [ ] Use lower and upper bounds to check for the feasibility of the problem in NN
- [x] Improve theory propagation (simple bounds could imply other bounds, in a chain fashion)
- [ ] Improve theory propagation even more
- [ ] Add support for LRA
- [x] Use a static array in the Variable class to store the name (and bounds?) of the variable. Use the variable id to
  access it. The position 0 can be reserved for "dummy".
- [ ] Refactor solvers
- [ ] Standardize infeasibility explanation

## TACAS

- [x] Fix references
- [x] Use american english
- [x] Expand the abstract. Why you'd want to use this tool?
- [x] Start the introduction with the importance of SAT/SMT solvers (and LP?)
- [x] At the end of the introduction add a paragraph on the structure of the paper
- [x] Add a survey of the state of the art SMT solvers
- [x] Move current technical introduction to another section (Preliminaries)
- [ ] Artifact evaluation

## Future work

- [ ] Naive implementation of the rational simplex algorithm for SMT solvers
  - [ ] Can it support iterative refinement or precision boosting?
- [ ] Specialise symbolic representation for LRA
- [ ] Extend cvc5 (or Z3) to use SoPlex as the theory solver
- [ ] Investigate over-approximation techniques for neural networks verification
