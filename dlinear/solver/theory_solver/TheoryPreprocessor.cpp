/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryPreprocessor.h"

#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/util/error.h"

namespace dlinear {
TheoryPreprocessor::TheoryPreprocessor(const TheorySolver &theory_solver, const std::string &class_name)
    : theory_solver_{theory_solver},
      stats_{theory_solver.config().with_timings(), class_name, "Total time spent in Process", "Total # of Process"} {}

template <SizedTypedIterable<Literal> Iterable>
void TheoryPreprocessor::AddLiterals(const Iterable &literals) {
  for (const Literal &lit : literals) AddLiteral(lit);
}
bool TheoryPreprocessor::WillRunOnStep(const Config::ExecutionStep step) const { return run_on_step() & step; }
void TheoryPreprocessor::AddLiteral(const Literal &) {}
void TheoryPreprocessor::AddVariable(const Variable &) {}

template <SizedTypedIterable<Literal> Iterable>
bool TheoryPreprocessor::EnableLiterals(const Iterable &theory_literals, const ConflictCallback &conflict_cb) {
  bool res = true;
  for (const Literal &lit : theory_literals) {
    res &= EnableLiteral(lit, conflict_cb);
  }
  return res;
}
bool TheoryPreprocessor::Process(const Config::ExecutionStep current_step, const ConflictCallback &conflict_cb) {
  DLINEAR_ASSERT(run_on_step() != Config::ExecutionStep::NEVER, "Process should not be called if set to NEVER");
  // In case the preprocessor is not supposed to run at this step, simply return true
  if (!WillRunOnStep(current_step)) return true;
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return ProcessCore(conflict_cb);
}

template void TheoryPreprocessor::AddLiterals(const std::vector<Literal> &);
template void TheoryPreprocessor::AddLiterals(const LiteralSet &);
template void TheoryPreprocessor::AddLiterals(const std::span<Literal> &);
template bool TheoryPreprocessor::EnableLiterals(const std::vector<Literal> &, const ConflictCallback &);
template bool TheoryPreprocessor::EnableLiterals(const LiteralSet &, const ConflictCallback &);
template bool TheoryPreprocessor::EnableLiterals(const std::span<Literal> &, const ConflictCallback &);

}  // namespace dlinear
