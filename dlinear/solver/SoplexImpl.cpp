/**
 * @file SoplexImpl.cpp
 * @author dlinear
 * @date 25 Aug 2023
 * @copyright 2023 dlinear
 */

#include "SoplexImpl.h"

#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

#ifdef DLINEAR_CHECK_INTERRUPT
#include "dlinear/util/SignalHandlerGuard.h"
#include "dlinear/util/interrupt.h"
#endif

using std::pair;
using std::vector;
using tl::optional;

namespace dlinear {

Context::SoplexImpl::SoplexImpl() : Context::SoplexImpl{Config{}} {}

Context::SoplexImpl::SoplexImpl(const Config &config)
    : Context::Impl{config}, sat_solver_{config_}, theory_solver_{config_} {}

void Context::SoplexImpl::Assert(const Formula &f) {
  if (is_true(f)) {
    return;
  }
  if (box().empty()) {
    return;
  }
  if (is_false(f)) {
    box().set_empty();
    return;
  }
  // if (FilterAssertion(f, &box()) == FilterAssertionResult::NotFiltered) {
  DLINEAR_DEBUG_FMT("Context::SoplexImpl::Assert: {} is added.", f);
  IfThenElseEliminator ite_eliminator;
  const Formula no_ite{ite_eliminator.Process(f)};
  for (const Variable &ite_var : ite_eliminator.variables()) {
    // Note that the following does not mark `ite_var` as a model variable.
    AddToBox(ite_var);
  }
  stack_.push_back(no_ite);
  sat_solver_.AddFormula(no_ite);
  return;
#if 0
  } else {
    DLINEAR_DEBUG_FMT("Context::SoplexImpl::Assert: {} is not added.", f);
    DLINEAR_DEBUG_FMT("Box=\n{}", box());
    return;
  }
#endif
}  // namespace dlinear

optional<Box> Context::SoplexImpl::CheckSatCore(const ScopedVector<Formula> &stack, Box box,
                                                mpq_class * /*actual_precision*/) {
  DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore()");
  DLINEAR_TRACE_FMT("Context::SoplexImpl::CheckSat: Box =\n{}", box);
  if (box.empty()) {
    return {};
  }
  // If false ∈ stack, it's UNSAT.
  for (const auto &f : stack.get_vector()) {
    if (is_false(f)) {
      return {};
    }
  }
  // If stack = ∅ or stack = {true}, it's trivially SAT.
  if (stack.empty() || (stack.size() == 1 && is_true(stack.first()))) {
    DLINEAR_DEBUG_FMT("Context::SoplexImpl::CheckSatCore() - Found Model\n{}", box);
    return box;
  }
#ifdef dlinear_check_interrupt
  // install a signal handler for sigint for this scope.
  signalhandlerguard guard{sigint, interrupt_handler, &g_interrupted};
#endif
  bool have_unsolved = false;
  while (true) {
    // Note that 'DLINEAR_CHECK_INTERRUPT' is only defined in setup.py,
    // when we build dReal python package.
#ifdef DLINEAR_CHECK_INTERRUPT
    if (g_interrupted) {
      DLINEAR_DEBUG("KeyboardInterrupt(SIGINT) Detected.");
      throw std::runtime_error("KeyboardInterrupt(SIGINT) Detected.");
    }
#endif

    // The box is passed in to the SAT solver solely to provide the LP solver
    // with initial bounds on the numerical variables.
    const auto optional_model = sat_solver_.CheckSat(box);
    if (optional_model) {
      const vector<pair<Variable, bool>> &boolean_model{optional_model->first};
      for (const pair<Variable, bool> &p : boolean_model) {
        // Here, we modify Boolean variables only (not used by the LP solver).
        box[p.first] = p.second ? 1 : 0;  // true -> 1 and false -> 0
      }
      const vector<pair<Variable, bool>> &theory_model{optional_model->second};
      if (!theory_model.empty()) {
        // SAT from SATSolver.
        DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore() - Sat Check = SAT");

        // The selected assertions have already been enabled in the LP solver
        int theory_result{theory_solver_.CheckSat(box, theory_model, sat_solver_.GetLinearSolverPtr(),
                                                  sat_solver_.GetLowerBounds(), sat_solver_.GetUpperBounds(),
                                                  sat_solver_.GetLinearVarMap())};
        if (theory_result == SAT_DELTA_SATISFIABLE) {
          // SAT from TheorySolver.
          DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore() - Theory Check = delta-SAT");
          Box model{theory_solver_.GetModel()};
          return model;
        } else {
          if (theory_result == SAT_UNSATISFIABLE) {
            // UNSAT from TheorySolver.
            DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore() - Theory Check = UNSAT");
          } else {
            DLINEAR_ASSERT(theory_result == SAT_UNSOLVED, "theory must be unsolved");
            DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore() - Theory Check = UNKNOWN");
            have_unsolved = true;  // Will prevent return of UNSAT
          }
          const LiteralSet &explanation{theory_solver_.GetExplanation()};
          DLINEAR_DEBUG_FMT(
              "Context::SoplexImpl::CheckSatCore() - size of explanation = {} - stack "
              "size = {}",
              explanation.size(), stack.get_vector().size());
          sat_solver_.AddLearnedClause(explanation);
        }
      } else {
        return box;
      }
    } else {
      if (have_unsolved) {
        // Can't assert UNSAT, because some branches were unsolved.
        DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore() - Sat Check = UNKNOWN");
        DLINEAR_RUNTIME_ERROR("LP solver failed to solve some instances");
      }
      // UNSAT from SATSolver. Escape the loop.
      DLINEAR_DEBUG("Context::SoplexImpl::CheckSatCore() - Sat Check = UNSAT");
      return {};
    }
  }
}

int Context::SoplexImpl::CheckOptCore(const ScopedVector<Formula> & /*stack*/, mpq_class * /*obj_lo*/,
                                      mpq_class * /*obj_up*/, Box * /*model*/) {
  DLINEAR_RUNTIME_ERROR("Not implemented.");
}

void Context::SoplexImpl::MinimizeCore(const Expression & /*obj_expr*/) { DLINEAR_RUNTIME_ERROR("Not implemented."); }

void Context::SoplexImpl::Pop() {
  DLINEAR_DEBUG("Context::SoplexImpl::Pop()");
  stack_.pop();
  boxes_.pop();
  sat_solver_.Pop();
}

void Context::SoplexImpl::Push() {
  DLINEAR_DEBUG("Context::SoplexImpl::Push()");
  sat_solver_.Push();
  boxes_.push();
  boxes_.push_back(boxes_.last());
  stack_.push();
}
}  // namespace dlinear
