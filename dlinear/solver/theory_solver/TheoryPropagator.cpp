/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryPropagator.h"

#include "dlinear/solver/theory_solver/TheorySolver.h"

namespace dlinear {
TheoryPropagator::TheoryPropagator(const TheorySolver &theory_solver, const std::string &class_name)
    : theory_solver_{theory_solver},
      stats_{theory_solver.config().with_timings(), class_name, "Total time spent in Propagate",
             "Total # of Propagate"} {}
}  // namespace dlinear
