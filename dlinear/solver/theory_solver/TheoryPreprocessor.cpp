/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryPreprocessor.h"

#include "dlinear/solver/theory_solver/TheorySolver.h"

namespace dlinear {
TheoryPreprocessor::TheoryPreprocessor(const TheorySolver &theory_solver, const std::string &class_name)
    : theory_solver_{theory_solver},
      stats_{theory_solver.config().with_timings(), class_name, "Total time spent in Process", "Total # of Process"} {}

}  // namespace dlinear
