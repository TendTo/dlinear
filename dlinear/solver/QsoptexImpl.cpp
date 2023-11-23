/**
 * @file QsoptexImpl.cpp
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 */

#include "QsoptexImpl.h"

#include <utility>

#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/logging.h"

#ifdef DLINEAR_PYDLINEAR
#include "dlinear/util/SignalHandlerGuard.h"
#include "dlinear/util/interrupt.h"
#endif

using std::pair;
using std::vector;

namespace dlinear {

Context::QsoptexImpl::QsoptexImpl() : Context::QsoptexImpl{Config{}} {}

Context::QsoptexImpl::QsoptexImpl(Config config)
    : Context::Impl{std::move(config)}, sat_solver_{config_}, theory_solver_{config_} {}

void Context::QsoptexImpl::Assert(const Formula &f) {
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
  DLINEAR_DEBUG_FMT("Context::QsoptexImpl::Assert: {} is added.", f);
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
    DLINEAR_DEBUG_FMT("Context::QsoptexImpl::Assert: {} is not added.", f);
    DLINEAR_DEBUG_FMT("Box=\n{}", box());
    return;
  }
#endif
}  // namespace dlinear

SatResult Context::QsoptexImpl::CheckSatCore(const ScopedVector<Formula> &stack, Box *box_,
                                             mpq_class *actual_precision) {
  Box &box{*box_};
  DLINEAR_TRACE_FMT("Context::QsoptexImpl::CheckSatCore: Box =\n{}", box);
  if (box.empty()) {
    return SAT_UNSATISFIABLE;
  }
  // If false ∈ stack, it's UNSAT.
  for (const auto &f : stack.get_vector()) {
    if (is_false(f)) {
      return SAT_UNSATISFIABLE;
    }
  }
  // If stack = ∅ or stack = {true}, it's trivially SAT.
  if (stack.empty() || (stack.size() == 1 && is_true(stack.first()))) {
    DLINEAR_DEBUG_FMT("Context::QsoptexImpl::CheckSatCore() - Found Model\n{}", box);
    return SAT_SATISFIABLE;
  }
#ifdef DLINEAR_PYDLINEAR
  // Install a signal handler for SIGINT for this scope.
  SignalHandlerGuard guard{SIGINT, interrupt_handler, &g_interrupted};
#endif
  bool have_unsolved = false;
  while (true) {
    // Note that 'DLINEAR_PYDLINEAR' is only defined in setup.py,
    // when we build dReal python package.
#ifdef DLINEAR_PYDLINEAR
    if (g_interrupted) {
      DLINEAR_DEBUG("KeyboardInterrupt(SIGINT) Detected.");
      throw std::runtime_error("KeyboardInterrupt(SIGINT) Detected.");
    }
#endif

    // The box is passed in to the SAT solver solely to provide the LP solver
    // with initial bounds on the numerical variables.
    DLINEAR_ASSERT(!have_objective_, "Unexpected objective");
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
        DLINEAR_DEBUG("Context::QsoptexImpl::CheckSatCore() - Sat Check = SAT");

        // The selected assertions (and objective function, where applicable)
        // have already been enabled in the LP solver
        int theory_result{theory_solver_.CheckSat(box, theory_model, sat_solver_.GetLinearSolver(),
                                                  sat_solver_.GetLinearVarMap(), actual_precision)};
        if (theory_result == SAT_DELTA_SATISFIABLE || theory_result == SAT_SATISFIABLE) {
          // SAT from TheorySolver.
          DLINEAR_DEBUG("Context::QsoptexImpl::CheckSatCore() - Theory Check = delta-SAT");
          box = theory_solver_.GetModel();
          return static_cast<SatResult>(theory_result);
        } else {
          if (theory_result == SAT_UNSATISFIABLE) {
            // UNSAT from TheorySolver.
            DLINEAR_DEBUG("Context::QsoptexImpl::CheckSatCore() - Theory Check = UNSAT");
          } else {
            DLINEAR_ASSERT(theory_result == SAT_UNSOLVED,
                           "Unexpected result from TheorySolver instead of SAT_UNSOLVED");
            DLINEAR_DEBUG("Context::QsoptexImpl::CheckSatCore() - Theory Check = UNKNOWN");
            have_unsolved = true;  // Will prevent return of UNSAT
          }
          // Force SAT solver to find new regions
          const LiteralSet &explanation{theory_solver_.GetExplanation()};
          DLINEAR_DEBUG_FMT("Context::QsoptexImpl::CheckSatCore() - size of explanation = {} - stack size = {}",
                            explanation.size(), stack.get_vector().size());
          sat_solver_.AddLearnedClause(explanation);
        }
      } else {
        return SAT_SATISFIABLE;
      }
    } else {
      if (have_unsolved) {
        // Can't assert UNSAT, because some branches were unsolved.
        DLINEAR_DEBUG("Context::QsoptexImpl::CheckSatCore() - Sat Check = UNKNOWN");
        DLINEAR_RUNTIME_ERROR("LP solver failed to solve some instances");
      }
      // UNSAT from SATSolver. Escape the loop.
      DLINEAR_DEBUG("Context::QsoptexImpl::CheckSatCore() - Sat Check = UNSAT");
      return SAT_UNSATISFIABLE;
    }
  }
}

int Context::QsoptexImpl::CheckOptCore(const ScopedVector<Formula> &stack, mpq_class *obj_lo, mpq_class *obj_up,
                                       Box *box) {
  DLINEAR_TRACE_FMT("Context::QsoptexImpl::CheckOpt: Box =\n{}", *box);
  if (box->empty()) {
    return LP_INFEASIBLE;
  }
  // If false ∈ stack, it's UNSAT (i.e. infeasible).
  for (const auto &f : stack.get_vector()) {
    if (is_false(f)) {
      return LP_INFEASIBLE;
    }
  }
  // If stack = ∅ or stack = {true}, it's trivially SAT - but we still need to
  // optimize!
  // if (stack.empty() || (stack.size() == 1 && is_true(stack.first()))) {
  //  DLINEAR_DEBUG_FMT("Context::QsoptexImpl::CheckOptCore() - Found Model\n{}", *box);
  //  return *box;
  //}
  bool have_unsolved = false;
  LpResult have_opt_cand = LP_NO_RESULT;  // optimality candidate
  mpq_class new_obj_up, new_obj_lo;       // Upper and lower bounds of new optimality candidate
  while (true) {
    // Note that 'DLINEAR_PYDLINEAR' is only defined in setup.py,
    // when we build dReal python package.
#ifdef DLINEAR_PYDLINEAR
    if (g_interrupted) {
      DLINEAR_DEBUG("KeyboardInterrupt(SIGINT) Detected.");
      throw std::runtime_error("KeyboardInterrupt(SIGINT) Detected.");
    }
#endif

    // The box is passed in to the SAT solver solely to provide the LP solver
    // with initial bounds on the numerical variables.
    DLINEAR_ASSERT(have_objective_, "Unexpected objective");
    const auto optional_model = sat_solver_.CheckSat(*box, std::optional<Expression>(obj_expr_));
    if (optional_model) {
      const vector<pair<Variable, bool>> &boolean_model{optional_model->first};
      for (const pair<Variable, bool> &p : boolean_model) {
        // Here, we modify Boolean variables only (not used by the LP solver).
        (*box)[p.first] = p.second ? 1 : 0;  // true -> 1 and false -> 0
      }
      const vector<pair<Variable, bool>> &theory_model{optional_model->second};
      // It doesn't matter if theory_model_ is empty, because CheckOpt() can
      // handle the no-constraints and no-bounds case.  All necessary
      // information is passed through via sat_solver_.GetLinearSolver() and
      // sat_solver.GetLinearVarMap().

      // SAT from SATSolver.
      DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Sat Check = SAT");

      // The selected assertions (and objective function, where applicable)
      // have already been enabled in the LP solver.
      int theory_result{theory_solver_.CheckOpt(*box, &new_obj_lo, &new_obj_up, theory_model,
                                                sat_solver_.GetLinearSolver(), sat_solver_.GetLinearVarMap())};

      switch (theory_result) {
        case LP_DELTA_OPTIMAL:
        case LP_OPTIMAL:
          DLINEAR_DEBUG_FMT("Context::QsoptexImpl::CheckOptCore() - Theory Check = {}",
                            theory_result == LP_OPTIMAL ? "OPTIMAL" : "delta-OPTIMAL");
          // Within Context::Impl, the problem is always a minimization.
          if (!have_opt_cand || new_obj_lo < *obj_lo) {
            // This LP could yield the global optimum, which could therefore
            // be as low as new_obj_lo.
            *obj_lo = new_obj_lo;
          }
          if (!have_opt_cand || new_obj_up < *obj_up) {
            // The global optimum can't be higher than new_obj_up -
            // otherwise, it would certainly be beaten by the current LP's
            // optimum.
            *obj_up = new_obj_up;
            // Regardless of the model that we choose, it could be incorrect
            // (it may be that the global optimum can only be obtained in
            // another segment of the constraint space).
            // However, it makes sense to prefer the model corresponding to
            // the most recently adopted upper bound, as this bound is
            // directly related to the primal solution.  Also, this ensures
            // that the model's objective value is always within the returned
            // range.
            *box = theory_solver_.GetModel();
          }
          have_opt_cand = static_cast<LpResult>(theory_result);
          break;
        case LP_UNBOUNDED:
          DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Theory Check = UNBOUNDED");
          // Result is correct - can return immediately.
          return LP_UNBOUNDED;
        case LP_INFEASIBLE:
          DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Theory Check = INFEASIBLE");
          // Must continue - to ensure that all regions are infeasible.
          break;
        case LP_UNSOLVED:
          DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Theory Check = UNKNOWN");
          have_unsolved = true;  // Will prevent return of INFEASIBLE or delta-OPTIMAL.
          // Problem may still be found to be unbounded.
          break;
        default:
          DLINEAR_UNREACHABLE();
      }

      // Force SAT solver to find new regions.
      const LiteralSet &explanation{theory_solver_.GetExplanation()};
      DLINEAR_DEBUG_FMT("Context::QsoptexImpl::CheckOptCore() - size of explanation = {} - stack size = {}",
                        explanation.size(), stack.get_vector().size());
      sat_solver_.AddLearnedClause(explanation);

    } else {
      // UNSAT from SATSolver. Must escape the loop, one way or another.
      if (have_unsolved) {
        // Can't assert infeasible or optimal, because some branches were unsolved.
        DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Sat Check = UNKNOWN");
        DLINEAR_RUNTIME_ERROR("LP solver failed to solve some instances");
      } else if (have_opt_cand) {
        DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Sat Check = delta-OPTIMAL");
        return LP_DELTA_OPTIMAL;
      } else {
        DLINEAR_DEBUG("Context::QsoptexImpl::CheckOptCore() - Sat Check = INFEASIBLE");
        return LP_INFEASIBLE;
      }
    }
  }
}

void Context::QsoptexImpl::MinimizeCore(const Expression &obj_expr) {
  DLINEAR_DEBUG_FMT("ContextImpl::Minimize(): Objective function is {}", obj_expr.to_string());
  obj_expr_ = obj_expr;
  have_objective_ = true;
}

void Context::QsoptexImpl::Pop() {
  DLINEAR_DEBUG("Context::QsoptexImpl::Pop()");
  stack_.pop();
  boxes_.pop();
  sat_solver_.Pop();
}

void Context::QsoptexImpl::Push() {
  DLINEAR_DEBUG("Context::QsoptexImpl::Push()");
  sat_solver_.Push();
  boxes_.push();
  boxes_.push_back(boxes_.last());
  stack_.push();
}
}  // namespace dlinear
