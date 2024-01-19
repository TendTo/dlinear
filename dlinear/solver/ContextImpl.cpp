/**
 * @file ContextImpl.cpp
 * @author dlinear
 * @date 14 Aug 2023
 * @copyright 2023 dlinear
 */

#include "ContextImpl.h"

#include <utility>

#include "dlinear/solver/DeltaQsoptexTheorySolver.h"
#include "dlinear/solver/DeltaSoplexTheorySolver.h"
#include "dlinear/solver/PicosatSatSolver.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/util/logging.h"

using std::pair;
using std::string;
using std::unordered_set;
using std::vector;

namespace {

bool ParseBooleanOption([[maybe_unused]] const string &key, const string &val) {
  if (val == "true") return true;
  if (val == "false") return false;
  DLINEAR_RUNTIME_ERROR_FMT("Unknown value {} is provided for option {}", val, key);
}

}  // namespace

namespace dlinear {

Context::Impl::Impl() : Impl{Config{}} {}

Context::Impl::Impl(const Config &config)
    : config_{config},
      have_objective_{false},
      is_max_{false},
      theory_loaded_{false},
      sat_solver_{std::make_unique<PicosatSatSolver>(predicate_abstractor_, config)},
      theory_solver_{GetTheorySolver(config)} {
  boxes_.push_back(Box{});
}

Context::Impl::Impl(Config &&config)
    : config_{std::move(config)},
      have_objective_{false},
      is_max_{false},
      theory_loaded_{false},
      sat_solver_{std::make_unique<PicosatSatSolver>(predicate_abstractor_, config)},
      theory_solver_{GetTheorySolver(config)} {
  boxes_.push_back(Box{});
}

void Context::Impl::Assert(const Formula &f) {
  if (is_true(f)) return;     // Skip trivially true assertions.
  if (box().empty()) return;  // The box has no variables, so skip.
  if (is_false(f)) {          // The formula is false, so set the box to empty. There is no point in continuing
    box().set_empty();
    return;
  }

#if 0
  if (FilterAssertion(f, &box()) == FilterAssertionResult::NotFiltered) {
#endif
  DLINEAR_DEBUG_FMT("ContextImpl::Assert: {} is added.", f);
  IfThenElseEliminator ite_eliminator;
  const Formula no_ite{ite_eliminator.Process(f)};

  // Note that the following does not mark `ite_var` as a model variable.
  for (const Variable &ite_var : ite_eliminator.variables()) AddToBox(ite_var);
  stack_.push_back(no_ite);
  sat_solver_->AddFormula(no_ite);
#if 0
  } else {
    DLINEAR_DEBUG_FMT("ContextImpl::Assert: {} is not added.", f);
    DLINEAR_DEBUG_FMT("Box=\n{}", box());
    return;
  }
#endif
}

void Context::Impl::Pop() {
  DLINEAR_DEBUG("ContextImpl::Pop()");
  stack_.pop();
  boxes_.pop();
  sat_solver_->Pop();
}

void Context::Impl::Push() {
  DLINEAR_DEBUG("ContextImpl::Push()");
  sat_solver_->Push();
  boxes_.push();
  boxes_.push_back(boxes_.last());
  stack_.push();
}

SatResult Context::Impl::CheckSat(mpq_class *precision) {
  SatResult result = CheckSatCore(precision);
  switch (result) {
    case SatResult::SAT_DELTA_SATISFIABLE:
    case SatResult::SAT_SATISFIABLE:
      model_ = ExtractModel(box());
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSat() - Found Model\n{}", model_);
      break;
    case SatResult::SAT_UNSATISFIABLE:
      DLINEAR_DEBUG("ContextImpl::CheckSat() - Model not found");
      model_.set_empty();
      break;
    case SatResult::SAT_UNSOLVED:
      DLINEAR_DEBUG("ContextImpl::CheckSat() - Unknown");
      model_.set_empty();
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  return result;
}

LpResult Context::Impl::CheckOpt(mpq_class *obj_lo, mpq_class *obj_up) {
  LpResult result = CheckOptCore(obj_lo, obj_up);
  if (LpResult::LP_DELTA_OPTIMAL == result || LpResult::LP_OPTIMAL == result) {
    model_ = ExtractModel(box());
    DLINEAR_DEBUG_FMT("ContextImpl::CheckOpt() - Found Model\n{}", model_);
  } else {
    DLINEAR_DEBUG("ContextImpl::CheckOpt() - Model not found");
    model_.set_empty();
  }
  return result;
}

void Context::Impl::AddToBox(const Variable &v) {
  DLINEAR_DEBUG_FMT("ContextImpl::AddToBox({})", v);
  if (!box().has_variable(v)) box().Add(v);
}

void Context::Impl::DeclareVariable(const Variable &v, const bool is_model_variable) {
  DLINEAR_DEBUG_FMT("ContextImpl::DeclareVariable({})", v);
  AddToBox(v);
  if (is_model_variable) MarkModelVariable(v);
}

void Context::Impl::SetDomain(const Variable &v, const Expression &lb, const Expression &ub) {
  DLINEAR_TRACE_FMT("ContextImpl::SetDomain({}, [{}, {}])", v, lb, ub);
  const mpq_class &lb_fp = lb.Evaluate();
  const mpq_class &ub_fp = ub.Evaluate();
  SetInterval(v, lb_fp, ub_fp);
}

void Context::Impl::Minimize(const vector<Expression> &functions) {
  DLINEAR_ASSERT(functions.size() == 1, "Must have exactly one objective function");

  const Expression &obj_expr{functions[0].Expand()};

  is_max_ = false;
  MinimizeCore(obj_expr);
}

void Context::Impl::Maximize(const vector<Expression> &functions) {
  DLINEAR_ASSERT(functions.size() == 1, "Must have exactly one objective function");

  // Negate objective function
  const Expression &obj_expr{(-functions[0]).Expand()};

  is_max_ = true;
  MinimizeCore(obj_expr);
}

void Context::Impl::SetInfo(const string &key, const double val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = fmt::format("{}", val);
}

void Context::Impl::SetInfo(const string &key, const string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = val;
}

void Context::Impl::SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInterval({} = [{}, {}])", v, lb, ub);
  box()[v] = Box::Interval{lb, ub};
}

void Context::Impl::SetLogic(const Logic &logic) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetLogic({})", logic);
  logic_ = logic;
}

void Context::Impl::SetOption(const string &key, const double val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = fmt::format("{}", val);

  if (key == ":precision") {
    if (val <= 0.0) DLINEAR_RUNTIME_ERROR_FMT("Precision has to be positive (input = {}).", val);
    return config_.mutable_precision().set_from_file(val);
  }
}

void Context::Impl::SetOption(const string &key, const string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = val;
  if (key == ":polytope") return config_.mutable_use_polytope().set_from_file(ParseBooleanOption(key, val));
  if (key == ":forall-polytope")
    return config_.mutable_use_polytope_in_forall().set_from_file(ParseBooleanOption(key, val));
  if (key == ":local-optimization")
    return config_.mutable_use_local_optimization().set_from_file(ParseBooleanOption(key, val));
  if (key == ":worklist-fixpoint")
    return config_.mutable_use_worklist_fixpoint().set_from_file(ParseBooleanOption(key, val));
  if (key == ":produce-models") return config_.mutable_produce_models().set_from_file(ParseBooleanOption(key, val));
}

Box Context::Impl::ExtractModel(const Box &box) const {
  if (static_cast<int>(model_variables_.size()) == box.size()) {
    // Every variable is a model variable. Simply return the @p box.
    return box;
  }
  Box new_box;
  for (const Variable &v : box.variables()) {
    if (IsModelVariable(v)) {
      new_box.Add(v, box[v].lb(), box[v].ub());
    }
  }
  return new_box;
}

bool Context::Impl::IsModelVariable(const Variable &v) const {
  return model_variables_.find(v.get_id()) != model_variables_.end();
}

void Context::Impl::MarkModelVariable(const Variable &v) { model_variables_.insert(v.get_id()); }

const ScopedVector<Formula> &Context::Impl::assertions() const { return stack_; }

bool Context::Impl::have_objective() const { return have_objective_; }

bool Context::Impl::is_max() const { return is_max_; }

SatResult Context::Impl::CheckSatCore(mpq_class *actual_precision) {
  DLINEAR_DEBUG("ContextImpl::CheckSatCore()");
  if (!theory_loaded_) {
    DLINEAR_DEBUG("ContextImpl::CheckSatCore(): Loading theory solver");
    theory_solver_->AddLiterals(sat_solver_->theory_literals());
    theory_loaded_ = true;
  }
  DLINEAR_TRACE_FMT("ContextImpl::CheckSat: Box =\n{}", box());
  if (box().empty()) {
    DLINEAR_DEBUG("ContextImpl::CheckSat: Box is empty");
    return SatResult::SAT_UNSATISFIABLE;
  }
  // If false ∈ stack, it's UNSAT.
  for (const auto &f : stack_.get_vector()) {
    if (is_false(f)) {
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSat: Found false formula = {}", f);
      return SatResult::SAT_UNSATISFIABLE;
    }
  }
  // If stack = ∅ or stack = {true}, it's trivially SAT.
  //  std::all_of(stack_.get_vector().begin(), stack_.get_vector().end(), drake::symbolic::is_true);
  if (stack_.empty() || (stack_.size() == 1 && is_true(stack_.first()))) {
    DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - Found Model\n{}", box());
    return SatResult::SAT_SATISFIABLE;
  }
#ifdef DLINEAR_PYDLINEAR
  // install a signal handler for sigint for this scope.
  signalhandlerguard guard{sigint, interrupt_handler, &g_interrupted};
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
    const auto optional_model = sat_solver_->CheckSat();

    // The SAT solver did not return a model.
    if (!optional_model) {
      if (have_unsolved) {  // There was an unsolved theory instance. The SMT solver failed to prove UNSAT.
        DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Sat Check = UNKNOWN");
        DLINEAR_RUNTIME_ERROR("LP solver failed to solve some instances");
      } else {  // There is no unsolved theory instance. The SAT solver succeeded in proving UNSAT.
        DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Sat Check = UNSAT");
        return SatResult::SAT_UNSATISFIABLE;
      }
    }

    // The SAT solver found a model that satisfies the formula. SAT from SATSolver.
    DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Sat Check = SAT");

    // Here, we modify Boolean variables only (not used by the LP solver).
    const vector<pair<Variable, bool>> &boolean_model{optional_model->first};
    for (const pair<Variable, bool> &p : boolean_model) {
      box()[p.first] = p.second ? 1 : 0;  // true -> 1 and false -> 0
    }

    // Extrapolate the theory model from the SAT model.
    const vector<pair<Variable, bool>> &theory_model{optional_model->second};
    // If there is no theory to solve, the SAT solver output is enough to return SAT.
    if (theory_model.empty()) return SatResult::SAT_SATISFIABLE;

    theory_solver_->Reset(box());
    theory_solver_->EnableLiterals(theory_model);

    // If the SAT solver found a model, we have to check if it is consistent with the theory
    SatResult theory_result = theory_solver_->CheckSat(box(), actual_precision);
    if (theory_result == SatResult::SAT_DELTA_SATISFIABLE || theory_result == SatResult::SAT_SATISFIABLE) {
      // SAT from TheorySolver.
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - Theory Check = {}", theory_result);
      box() = theory_solver_->GetModel();
      return theory_result;
    } else {
      if (theory_result == SatResult::SAT_UNSATISFIABLE) {
        // UNSAT from TheorySolver.
        DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Theory Check = UNSAT");
      } else {
        DLINEAR_ASSERT(theory_result == SatResult::SAT_UNSOLVED, "theory must be unsolved");
        DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Theory Check = UNKNOWN");
        have_unsolved = true;  // Will prevent return of UNSAT
      }
      const LiteralSet &explanation{theory_model.cbegin(), theory_model.cend()};
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - size of explanation = {} - stack size = {}", explanation.size(),
                        stack_.get_vector().size());
      sat_solver_->AddLearnedClause(explanation);
    }
  }
}

LpResult Context::Impl::CheckOptCore([[maybe_unused]] mpq_class *obj_lo, [[maybe_unused]] mpq_class *obj_up) {
  DLINEAR_RUNTIME_ERROR("Not implemented");
  return LpResult::LP_INFEASIBLE;
}
void Context::Impl::MinimizeCore([[maybe_unused]] const Expression &obj_expr) {
  DLINEAR_RUNTIME_ERROR("Not implemented");
}
std::unique_ptr<TheorySolver> Context::Impl::GetTheorySolver(const Config &config) {
  switch (config.lp_solver()) {
    case Config::LPSolver::SOPLEX:
      return config.precision() >= 0 ? std::make_unique<DeltaSoplexTheorySolver>(predicate_abstractor_, config)
                                     : nullptr;
    case Config::LPSolver::QSOPTEX:
      return config.precision() >= 0 ? std::make_unique<DeltaQsoptexTheorySolver>(predicate_abstractor_, config)
                                     : nullptr;
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
