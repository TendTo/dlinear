/**
 * @file ContextImpl.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "ContextImpl.h"

#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

#ifdef DLINEAR_ENABLED_QSOPTEX
#include "dlinear/solver/DeltaQsoptexTheorySolver.h"
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
#include "dlinear/solver/CompleteSoplexTheorySolver.h"
#include "dlinear/solver/DeltaSoplexTheorySolver.h"
#endif
#include "dlinear/solver/PicosatSatSolver.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/OptionValue.hpp"
#include "dlinear/util/Stats.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace {

bool ParseBooleanOption([[maybe_unused]] const std::string &key, const std::string &val) {
  if (val == "true") return true;
  if (val == "false") return false;
  DLINEAR_INVALID_ARGUMENT_EXPECTED(key, val, "bool [true, false]");
}
double ParseDoubleOption([[maybe_unused]] const std::string &key, const std::string &val) {
  try {
    return std::stod(val);
  } catch (const std::invalid_argument &e) {
    DLINEAR_INVALID_ARGUMENT_EXPECTED(key, val, "double");
  } catch (const std::out_of_range &e) {
    DLINEAR_OUT_OF_RANGE_FMT("Out of range value {} is provided for option {}. Expected double", val, key);
  }
}

}  // namespace

namespace dlinear {

Context::Impl::Impl(Config &config, SmtSolverOutput *const output)
    : config_{config},
      output_{output},
      logic_{},
      have_objective_{false},
      is_max_{false},
      theory_loaded_{false},
      predicate_abstractor_{config},
      sat_solver_{std::make_unique<PicosatSatSolver>(predicate_abstractor_)},
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

  DLINEAR_DEBUG_FMT("ContextImpl::Assert: {} is added.", f);
  IfThenElseEliminator ite_eliminator{config_};
  const Formula no_ite{ite_eliminator.Process(f)};

  // Note that the following does not mark `ite_var` as a model variable.
  for (const Variable &ite_var : ite_eliminator.variables()) AddToBox(ite_var);
  if (config_.with_timings() && output_ != nullptr) output_->ite_stats += ite_eliminator.stats();
  stack_.push_back(no_ite);
  sat_solver_->AddFormula(no_ite);
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
  if (!logic_.has_value()) DLINEAR_WARN("Logic is not set. Defaulting to QF_LRA.");
  if (config_.skip_check_sat()) {
    DLINEAR_DEBUG("ContextImpl::CheckOpt() - Skipping SAT check");
    UpdateAndPrintOutput(SmtResult::SKIP_SAT);
    return SatResult::SAT_NO_RESULT;
  }

  const SatResult result = CheckSatCore(precision);
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

  if (output_ == nullptr) return result;
  DLINEAR_DEBUG("ContextImpl::CheckSat() - Setting output");
  output_->actual_precision = *precision;
  UpdateAndPrintOutput(parse_smt_result(result));
  return result;
}

LpResult Context::Impl::CheckOpt(mpq_class *obj_lo, mpq_class *obj_up) {
  if (!logic_.has_value()) DLINEAR_WARN("Logic is not set. Defaulting to QF_LRA.");
  if (config_.skip_check_sat()) {
    DLINEAR_DEBUG("ContextImpl::CheckOpt() - Skipping SAT check");
    UpdateAndPrintOutput(SmtResult::SKIP_SAT);
    return LpResult::LP_NO_RESULT;
  }
  const LpResult result = CheckOptCore(obj_lo, obj_up);
  if (LpResult::LP_DELTA_OPTIMAL == result || LpResult::LP_OPTIMAL == result) {
    model_ = ExtractModel(box());
    DLINEAR_DEBUG_FMT("ContextImpl::CheckOpt() - Found Model\n{}", model_);
  } else {
    DLINEAR_DEBUG("ContextImpl::CheckOpt() - Model not found");
    model_.set_empty();
  }

  if (output_ == nullptr) return result;
  DLINEAR_DEBUG("ContextImpl::CheckSat() - Setting output");
  output_->lower_bound = *obj_lo;
  output_->upper_bound = *obj_up;
  UpdateAndPrintOutput(parse_smt_result(result));
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

void Context::Impl::Minimize(const Expression &obj_function) {
  is_max_ = false;
  MinimizeCore(obj_function);
}

void Context::Impl::Maximize(const Expression &obj_function) {
  is_max_ = true;
  MinimizeCore((-obj_function).Expand());
}

void Context::Impl::SetInfo(const std::string &key, const std::string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInfo({} ↦ {})", key, val);
  info_[key] = val;
}

std::string Context::Impl::GetInfo(const std::string &key) const {
  const auto it = info_.find(key);
  if (it == info_.end()) return "";
  return it->second;
}

void Context::Impl::SetInterval(const Variable &v, const mpq_class &lb, const mpq_class &ub) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetInterval({} = [{}, {}])", v, lb, ub);
  if (lb > ub) DLINEAR_RUNTIME_ERROR_FMT("Lower bound {} is greater than upper bound {}.", lb, ub);
  box()[v] = Interval{lb, ub};
}

void Context::Impl::SetLogic(const Logic logic) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetLogic({})", logic);
  switch (logic) {
    case Logic::QF_LRA:
      logic_ = logic;
      break;
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported logic: {}", logic);
  }
}

void Context::Impl::SetOption(const std::string &key, const std::string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = val;
  if (key == ":precision") config_.m_precision().set_from_file(ParseDoubleOption(key, val));
  if (key == ":polytope") return config_.m_use_polytope().set_from_file(ParseBooleanOption(key, val));
  if (key == ":forall-polytope") return config_.m_use_polytope_in_forall().set_from_file(ParseBooleanOption(key, val));
  if (key == ":local-optimization")
    return config_.m_use_local_optimization().set_from_file(ParseBooleanOption(key, val));
  if (key == ":worklist-fixpoint") return config_.m_use_worklist_fixpoint().set_from_file(ParseBooleanOption(key, val));
  if (key == ":produce-models") return config_.m_produce_models().set_from_file(ParseBooleanOption(key, val));
}

std::string Context::Impl::GetOption(const std::string &key) const {
  if (key == ":polytope") return fmt::format("{}", config_.use_polytope());
  if (key == ":forall-polytope") return fmt::format("{}", config_.use_polytope_in_forall());
  if (key == ":local-optimization") return fmt::format("{}", config_.use_local_optimization());
  if (key == ":worklist-fixpoint") return fmt::format("{}", config_.use_worklist_fixpoint());
  if (key == ":produce-models") return fmt::format("{}", config_.produce_models());
  if (key == ":precision") return fmt::format("{}", config_.precision());
  const auto it = option_.find(key);
  if (it == option_.end()) return "";
  return it->second;
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

    DLINEAR_WARN("New iteration");
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

    // Extrapolate the boolean and theory model from the SAT model.
    const std::vector<Literal> &boolean_model{optional_model->first};
    const std::vector<Literal> &theory_model{optional_model->second};

    // Update the Boolean variables in the model (not used by the LP solver).
    for (const auto &[var, truth] : boolean_model) {
      box()[var] = truth ? 1 : 0;  // true -> 1 and false -> 0
    }

    // If there is no theory to solve, the SAT solver output is enough to return SAT.
    if (theory_model.empty()) return SatResult::SAT_SATISFIABLE;

    theory_solver_->Reset(box());
    TheorySolver::Explanations bound_explanations = theory_solver_->EnableLiterals(theory_model);
    if (!bound_explanations.empty()) {
      DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Enable bound check = UNSAT");
      LearnExplanations(bound_explanations);
      continue;
    }

    TheorySolver::Explanations theory_explanations;
    // If the SAT solver found a model, we have to check if it is consistent with the theory
    SatResult theory_result = theory_solver_->CheckSat(box(), actual_precision, theory_explanations);
    if (theory_result == SatResult::SAT_DELTA_SATISFIABLE || theory_result == SatResult::SAT_SATISFIABLE) {
      // SAT from TheorySolver.
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - Theory Check = {}", theory_result);
      box() = theory_solver_->model();
      return theory_result;
    }

    if (theory_result == SatResult::SAT_UNSATISFIABLE) {  // UNSAT from TheorySolver.
      DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Theory Check = UNSAT");
    } else {
      DLINEAR_ASSERT(theory_result == SatResult::SAT_UNSOLVED, "theory must be unsolved");
      DLINEAR_ERROR("ContextImpl::CheckSatCore() - Theory Check = UNKNOWN");
      have_unsolved = true;  // Will prevent return of UNSAT
      theory_explanations.emplace(theory_model.cbegin(), theory_model.cend());
    }
    DLINEAR_ASSERT(!theory_explanations.empty(), "theory_explanations must not be empty");
    LearnExplanations(theory_explanations);
  }
}

LpResult Context::Impl::CheckOptCore([[maybe_unused]] mpq_class *obj_lo, [[maybe_unused]] mpq_class *obj_up) {
  DLINEAR_RUNTIME_ERROR("CheckOptCore() Not implemented");
}
void Context::Impl::MinimizeCore([[maybe_unused]] const Expression &obj_expr) {
  DLINEAR_RUNTIME_ERROR("MinimizeCore() Not implemented");
}
std::unique_ptr<TheorySolver> Context::Impl::GetTheorySolver(const Config &config) {
  switch (config.lp_solver()) {
#ifdef DLINEAR_ENABLED_QSOPTEX
    case Config::LPSolver::QSOPTEX:
      if (config.complete())  // TODO: add support for complete QSOPTEX
        return std::make_unique<DeltaQsoptexTheorySolver>(predicate_abstractor_);
      else
        return std::make_unique<DeltaQsoptexTheorySolver>(predicate_abstractor_);
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    case Config::LPSolver::SOPLEX:
      if (config.complete())
        return std::make_unique<CompleteSoplexTheorySolver>(predicate_abstractor_);
      else
        return std::make_unique<DeltaSoplexTheorySolver>(predicate_abstractor_);
#endif
    default:
      DLINEAR_UNREACHABLE();
  }
}
void Context::Impl::LearnExplanation(const LiteralSet &explanation) {
  DLINEAR_DEBUG_FMT("ContextImpl::LearnExplanation(): size of explanation = {} - stack size = {}", explanation.size(),
                    stack_.get_vector().size());
  DLINEAR_CRITICAL_FMT("ContextImpl::LearnExplanation({})", explanation);
  DLINEAR_ASSERT(!explanations_so_far.contains(explanation), "Explanation already present, looping!");
#ifndef NDEBUG
  explanations_so_far.insert(explanation);
#endif
  if (explanation.empty()) DLINEAR_RUNTIME_ERROR("No explanation is provided. Infinite loop detected.");
  sat_solver_->AddLearnedClause(explanation);
}

void Context::Impl::LearnExplanations(const TheorySolver::Explanations &explanations) {
  DLINEAR_ASSERT(!explanations.empty(), "Explanations cannot be empty");
  for (const LiteralSet &explanation : explanations) LearnExplanation(explanation);
}

void Context::Impl::UpdateAndPrintOutput(const SmtResult smt_result) const {
  if (output_ == nullptr) return;
  DLINEAR_DEBUG("ContextImpl::CheckOpt() - Setting output");
  output_->result = smt_result;
  output_->n_assertions = assertions().size();
  if (config_.produce_models()) output_->model = model_;
  if (config_.with_timings()) {
    DLINEAR_DEBUG("ContextImpl::CheckOpt() - Setting timings");
    output_->sat_stats = sat_solver_->stats();
    output_->theory_stats = theory_solver_->stats();
    output_->predicate_abstractor_stats = predicate_abstractor_.stats();
    output_->cnfizer_stats = sat_solver_->cnfizer_stats();
  }
  if (!config_.silent()) std::cout << *output_ << std::endl;
}

}  // namespace dlinear
