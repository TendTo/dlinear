/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "TheoryPropagator.h"

#include "dlinear/solver/theory_solver/TheorySolver.h"
#include "dlinear/util/error.h"

namespace dlinear {
TheoryPropagator::TheoryPropagator(const TheorySolver &theory_solver, const std::string &class_name)
    : theory_solver_{theory_solver},
      stats_{theory_solver.config().with_timings(), class_name, "Total time spent in Propagate",
             "Total # of Propagate"} {}

bool TheoryPropagator::WillRunOnStep(const Config::ExecutionStep step) const { return run_on_step() & step; }
void TheoryPropagator::Propagate(const Config::ExecutionStep current_step, const AssertCallback &assert_cb) {
  DLINEAR_ASSERT(run_on_step() != Config::ExecutionStep::NEVER, "Process should not be called if set to NEVER");
  // In case the preprocessor is not supposed to run at this step, simply return true
  if (!(current_step & run_on_step())) return;
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();
  return PropagateCore(assert_cb);
}

}  // namespace dlinear
