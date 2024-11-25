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

template <TypedIterable<Literal> Iterable>
bool TheoryPreprocessor::EnableLiterals(const Iterable &theory_literals, const ConflictCallback &conflict_cb) {
  bool res = true;
  for (const Literal &lit : theory_literals) {
    res &= EnableLiteral(lit, conflict_cb);
  }
  return res;
}

template bool TheoryPreprocessor::EnableLiterals(const std::vector<Literal> &, const ConflictCallback &);
template bool TheoryPreprocessor::EnableLiterals(const LiteralSet &, const ConflictCallback &);
template bool TheoryPreprocessor::EnableLiterals(const std::span<Literal> &, const ConflictCallback &);

}  // namespace dlinear
