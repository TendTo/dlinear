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
#include "dlinear/solver/CadicalSatSolver.h"
#include "dlinear/solver/PicosatSatSolver.h"
#include "dlinear/solver/ReluConstraint.h"
#include "dlinear/solver/SatResult.h"
#include "dlinear/solver/TheoryPropagator.h"
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
      model_{config_.lp_solver()},
      have_objective_{false},
      is_max_{false},
      predicate_abstractor_{config},
      ite_eliminator_{config},
      sat_solver_{GetSatSolver()},
      theory_solver_{GetTheorySolver()} {
  boxes_.push_back(Box{config_.lp_solver()});
}

void Context::Impl::Assert(const Formula &f) {
  if (is_true(f)) return;     // Skip trivially true assertions.
  if (box().empty()) return;  // The box has no variables, so skip.
  if (is_false(f)) {          // The formula is false, so set the box to empty. There is no point in continuing
    box().set_empty();
    return;
  }

  DLINEAR_DEBUG_FMT("ContextImpl::Assert({})", f);
  const Formula no_ite{ite_eliminator_.Process(f)};

  // Note that the following does not mark `ite_var` as a model variable.
  for (const auto &[ite_expr, ite_var] : ite_eliminator_.variables()) AddToBox(ite_var);
  stack_.push_back(no_ite);
  sat_solver_->AddFormula(no_ite);
}
Expression Context::Impl::AssertIte(const Expression &e) {
  if (!is_if_then_else(e)) return e;

  DLINEAR_TRACE_FMT("ContextImpl::AssertIte({})", e);
  const auto [no_ite, assertion] = ite_eliminator_.Process(e);

  if (Formula::True().EqualTo(assertion)) return no_ite;

  DLINEAR_ASSERT(is_variable(no_ite), "e must be a variable");
  // Note that the following does not mark `ite_var` as a model variable.
  AddToBox(to_variable(no_ite)->get_variable());
  stack_.push_back(assertion);
  sat_solver_->AddFormula(assertion);
  return no_ite;
}
Expression Context::Impl::AssertMax(const Expression &e) {
  if (!drake::symbolic::is_max(e)) return e;

  DLINEAR_TRACE_FMT("ContextImpl::AssertMax({})", e);
  const auto [no_ite_max, assertion] = ite_eliminator_.Process(e);
  DLINEAR_ASSERT(drake::symbolic::is_max(no_ite_max), "no_ite_max must be a max expression");

  const Expression &lhs = drake::symbolic::get_first_argument(no_ite_max);
  const Expression &rhs = drake::symbolic::get_second_argument(no_ite_max);

  DLINEAR_ASSERT(!lhs.EqualTo(rhs), "lhs must be different from rhs");

  if (!Formula::True().EqualTo(assertion)) {
    stack_.push_back(assertion);
    sat_solver_->AddFormula(assertion);
  }

  const Expression a1 = Expression(Variable{"a1 | " + e.to_string()});
  const Expression a2 = Expression(Variable{"a2 | " + e.to_string()});
  const Expression no_max = Expression(Variable{"no_max | " + e.to_string()});

  Assert(no_max - lhs == a1);
  Assert(no_max - rhs == a2);
  Assert(a1 >= 0);
  Assert(a2 >= 0);
  Assert(a1 <= 0 || a2 <= 0);
  // Note that the following does not mark the introduced variables as a model variable.
  AddToBox(to_variable(no_max)->get_variable());
  AddToBox(to_variable(a1)->get_variable());
  AddToBox(to_variable(a2)->get_variable());
  return no_max;
}
Expression Context::Impl::AssertRelu(const dlinear::drake::symbolic::Expression &e) {
  DLINEAR_ASSERT(is_if_then_else(e), "e must be an ITE expression");
  DLINEAR_ASSERT(!get_then_expression(e).include_ite(), "'then' branch of e must not include ITE expression");
  DLINEAR_ASSERT(!get_else_expression(e).include_ite(), "'else' branch of e must not include ITE expression");
  DLINEAR_TRACE_FMT("ContextImpl::AssertRelu({})", e);

  const auto [no_relu, assertion] = ite_eliminator_.Process(e);

  if (Formula::True().EqualTo(assertion)) return no_relu;

  DLINEAR_ASSERT(is_variable(no_relu), "no_relu must be a variable");

  // Note that the following does not mark `no_relu` as a model variable.
  AddToBox(to_variable(no_relu)->get_variable());
  stack_.push_back(assertion);
  sat_solver_->AddFormula(assertion);
  return no_relu;
}

GuidedConstraint &Context::Impl::AddGuidedConstraint(std::unique_ptr<GuidedConstraint> &&constraint) {
  return *guided_constraints_.emplace_back(std::move(constraint)).get();
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
    case Logic::LRA:
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported logic: {}", logic);
  }
}

void Context::Impl::SetOption(const std::string &key, const std::string &val) {
  DLINEAR_DEBUG_FMT("ContextImpl::SetOption({} ↦ {})", key, val);
  option_[key] = val;
  if (key == ":precision") config_.m_precision().set_from_file(ParseDoubleOption(key, val));
  if (key == ":produce-models") return config_.m_produce_models().set_from_file(ParseBooleanOption(key, val));
}

std::string Context::Impl::GetOption(const std::string &key) const {
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
  Box new_box{config_.lp_solver()};
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

  // Temporarily disable to study the effect of guided constraints
#if 0
    if (!config_.disable_theory_preprocessing()) {
      // Add some theory constraints to the SAT solver (e.g. (x > 0) => (x > -1))
      TheoryPropagator propagator{config_, [this](const Formula &f) { Assert(f); }, predicate_abstractor_};
      propagator.Propagate();
    }
#endif

  // Compute the fixed theory literals to avoid having to recompute them again and again.
  theory_solver_->AddLiterals();
  const std::set<LiteralSet> explanations{theory_solver_->AddFixedLiterals(sat_solver_->FixedTheoryLiterals())};
  if (!explanations.empty()) {
    DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Fixed bound check = UNSAT");
    LearnExplanations(explanations);
    return SatResult::SAT_UNSATISFIABLE;
  }
  // Make sure the theory solver is in sync with the current box.
  theory_solver_->Reset(box());

  // Check the current constraints to see if there is anything that could be used to use for the guided constraints
  for (const std::unique_ptr<GuidedConstraint> &constraint : guided_constraints_) {
    theory_solver_->m_preprocessor().EnableLiterals(constraint->enabled_literals());
  }
  theory_solver_->m_preprocessor().Process();
  for (std::unique_ptr<GuidedConstraint> &constraint : guided_constraints_) {
    DLINEAR_ASSERT(dynamic_cast<ReluConstraint *>(constraint.get()) != nullptr,
                   "Guided constraint must be a ReluConstraint");
    ReluConstraint &relu_constraint = static_cast<ReluConstraint &>(*constraint.get());
    const BoundVector &relu_bounds = theory_solver_->theory_bounds().at(relu_constraint.relu_var());
    relu_constraint.SetLowerBound(relu_bounds.active_lower_bound() >= 0 ? relu_bounds.active_lower_bound()
                                                                        : ReluConstraint::zero);
    relu_constraint.SetUpperBound(relu_bounds.active_upper_bound() >= 0 ? relu_bounds.active_upper_bound()
                                                                        : ReluConstraint::zero);
    fmt::println("Guided Constraint: {}", relu_bounds.GetActiveBoundsValue());
    DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - Adding guided constraint = {}", constraint->Assumptions());
    for (const Literal &learned_clause : constraint->LearnedClauses()) sat_solver_->AddLearnedClause(learned_clause);
  }
  theory_solver_->m_preprocessor().Clear(theory_solver_->fixed_preprocessor());

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
    const TheorySolver::Explanations bound_explanations{theory_solver_->EnableLiterals(theory_model)};
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
std::unique_ptr<TheorySolver> Context::Impl::GetTheorySolver() {
  switch (config_.lp_solver()) {
#ifdef DLINEAR_ENABLED_QSOPTEX
    case Config::LPSolver::QSOPTEX:
      if (config_.complete())  // TODO: add support for complete QSOPTEX
        return std::make_unique<DeltaQsoptexTheorySolver>(predicate_abstractor_);
      else
        return std::make_unique<DeltaQsoptexTheorySolver>(predicate_abstractor_);
#endif
#ifdef DLINEAR_ENABLED_SOPLEX
    case Config::LPSolver::SOPLEX:
      if (config_.complete())
        return std::make_unique<CompleteSoplexTheorySolver>(predicate_abstractor_);
      else
        return std::make_unique<DeltaSoplexTheorySolver>(predicate_abstractor_);
#endif
    default:
      DLINEAR_UNREACHABLE();
  }
}
std::unique_ptr<SatSolver> Context::Impl::GetSatSolver() {
  switch (config_.sat_solver()) {
#ifdef DLINEAR_ENABLED_CADICAL
    case Config::SatSolver::CADICAL:
      return std::make_unique<CadicalSatSolver>(predicate_abstractor_);
#endif
#ifdef DLINEAR_ENABLED_PICOSAT
    case Config::SatSolver::PICOSAT:
      return std::make_unique<PicosatSatSolver>(predicate_abstractor_);
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
  DLINEAR_ASSERT(!explanation.empty(), "No explanation is provided. Infinite loop detected.");
#ifndef NDEBUG
  explanations_so_far.insert(explanation);
#endif
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
