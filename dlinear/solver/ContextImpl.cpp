/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "ContextImpl.h"

#include <future>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

#include "dlinear/solver/sat_solver/CadicalSatSolver.h"
#include "dlinear/solver/sat_solver/PicosatSatSolver.h"
#include "dlinear/solver/sat_solver/SatResult.h"
#include "dlinear/solver/theory_solver/TheoryResult.h"
#include "dlinear/solver/theory_solver/qf_lra/CompleteLpTheorySolver.h"
#include "dlinear/solver/theory_solver/qf_lra/DeltaLpTheorySolver.h"
#include "dlinear/symbolic/IfThenElseEliminator.h"
#include "dlinear/symbolic/literal.h"
#include "dlinear/util/OptionValue.hpp"
#include "dlinear/util/Stats.h"
#include "dlinear/util/error.h"
#include "dlinear/util/logging.h"

#ifdef DLINEAR_PYDLINEAR
#include "pydlinear/interrupt.h"
#endif

namespace dlinear {

namespace {

bool ParseBooleanOption([[maybe_unused]] const std::string &key, const std::string &val) {
  if (val == "true") return true;
  if (val == "false") return false;
  DLINEAR_INVALID_ARGUMENT_EXPECTED(key, val, "bool [true, false]");
}
double ParseDoubleOption([[maybe_unused]] const std::string &key, const std::string &val) {
  try {
    return std::stod(val);
  } catch (const std::invalid_argument &) {
    DLINEAR_INVALID_ARGUMENT_EXPECTED(key, val, "double");
  } catch (const std::out_of_range &) {
    DLINEAR_OUT_OF_RANGE_FMT("Out of range value {} is provided for option {}. Expected double", val, key);
  }
}

#ifndef NDEBUG
std::unique_ptr<TheorySolver> debug_theory_solver;
const std::function<void(const LiteralSet &)> debug_conflict_cb = [](const LiteralSet &) {};
#endif

}  // namespace

Context::Impl::Impl(Config &config, SmtSolverOutput *const output)
    : config_{config},
      output_{output},
      interrupted_{false},
      logic_{},
      model_{config_.lp_solver()},
      have_objective_{false},
      is_max_{false},
      predicate_abstractor_{config},
      ite_eliminator_{config},
      conflict_cb_{[this](const Explanation &explanation) { LearnExplanation(explanation); }},
      assert_cb_{[this](const Formula &f) { sat_solver_->AddFormula(f); }},
      sat_solver_{GetSatSolver()},
      theory_solver_{GetTheorySolver()} {
  boxes_.push_back(Box{config_.lp_solver()});
#ifndef NDEBUG
  debug_theory_solver = config_.lp_solver() == Config::LPSolver::SOPLEX ? GetTheorySolver() : nullptr;
#endif
}

void Context::Impl::Assert(const Formula &f) {
  if (is_true(f)) return;  // Skip trivially true assertions.
  if (is_false(f)) {  // The formula is false. No point in adding it to the SAT solver. There is no point in continuing
    stack_.push_back(f);
    return;
  }

  DLINEAR_DEBUG_FMT("ContextImpl::Assert({})", f);
  const Formula no_ite{ite_eliminator_.Process(f)};

  // Note that the following does not mark `ite_var` as a model variable.
  for (const auto &[ite_expr, ite_var] : ite_eliminator_.variables()) AddToBox(ite_var);
  stack_.push_back(no_ite);
  sat_solver_->AddFormula(no_ite);
}
void Context::Impl::AssertPiecewiseLinearFunction(const Variable &var, const Formula &cond, const Expression &active,
                                                  const Expression &inactive) {
  DLINEAR_TRACE_FMT("ContextImpl::AssertPiecewiseLinearFunction({})", var);
  DLINEAR_ASSERT(!var.is_dummy() && var.get_type() == Variable::Type::CONTINUOUS, "Variable must be a real variable");
  DLINEAR_ASSERT(is_relational(cond), "Condition must be a relational formula");

  const Formula condition_lit = predicate_abstractor_(cond);
  const Formula active_lit = predicate_abstractor_(var - active == 0);
  const Formula inactive_lit = predicate_abstractor_(var - inactive == 0);
  // Make sure the cond is assigned a value (true or false) in the SAT solver
  const Formula force_assignment(condition_lit || !condition_lit);
  const Formula active_assertion{active_lit || !condition_lit};
  const Formula inactive_assertion{inactive_lit || condition_lit};

  DeclareVariable(var, false);
  stack_.push_back(force_assignment);
  stack_.push_back(active_assertion);
  stack_.push_back(inactive_assertion);
  sat_solver_->AddClause(force_assignment);
  sat_solver_->AddClause(active_assertion);
  sat_solver_->AddClause(inactive_assertion);
}

const PiecewiseLinearConstraint &Context::Impl::AddGuidedConstraint(
    std::unique_ptr<PiecewiseLinearConstraint> &&constraint) {
  return *pl_constraints_.emplace_back(std::move(constraint)).get();
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

SmtResult Context::Impl::CheckSat(mpq_class *precision) {
  if (!logic_.has_value()) DLINEAR_WARN("Logic is not set. Defaulting to QF_LRA.");
  DLINEAR_INFO("ContextImpl::CheckSat: Checking the satisfiability of the input");
  if (config_.skip_check_sat()) {
    DLINEAR_DEBUG("ContextImpl::CheckSat() - Skipping SAT check");
    UpdateAndPrintOutput(SmtResult::SKIP_SAT);
    return SmtResult::SKIP_SAT;
  }

  // Start timeout thread to interrupt the CheckSat loop if it takes too long
  interrupted_ = false;
  std::condition_variable check_sat_finished;
  std::future<void> timeout = std::async(std::launch::async, [this, &check_sat_finished]() -> void {
    std::mutex mutex;
    std::unique_lock<std::mutex> lock(mutex);
    check_sat_finished.wait_for(lock, std::chrono::milliseconds(config_.timeout()));
    if (config_.timeout() > 0) {
      DLINEAR_INFO_FMT("ContextImpl::CheckSat: The solver is taking longer than {}ms. Interrupting", config_.timeout());
      Interrupt();
    }
  });

  const SmtResult result = CheckSatCore(precision);
  switch (result) {
    case SmtResult::SAT:
    case SmtResult::DELTA_SAT:
      model_ = ExtractModel(box());
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSat() - Found Model\n{}", model_);
      break;
    case SmtResult::UNSAT:
      DLINEAR_DEBUG("ContextImpl::CheckSat() - Model not found");
      model_.set_empty();
      break;
    case SmtResult::ERROR:
      DLINEAR_DEBUG("ContextImpl::CheckSat() - Error");
      model_.set_empty();
      break;
    case SmtResult::TIMEOUT:
      DLINEAR_DEBUG("ContextImpl::CheckSat() - Timeout");
      model_.set_empty();
      break;
    default:
      DLINEAR_UNREACHABLE();
  }

  if (output_ == nullptr) return result;
  DLINEAR_DEBUG("ContextImpl::CheckSat() - Setting output");
  output_->actual_precision = *precision;
  UpdateAndPrintOutput(result);

  // Ensure the timer thread is stopped cleanly
  check_sat_finished.notify_all();
  timeout.wait();
  return result;
}

SmtResult Context::Impl::CheckOpt(mpq_class *obj_lo, mpq_class *obj_up) {
  if (!logic_.has_value()) DLINEAR_WARN("Logic is not set. Defaulting to QF_LRA.");
  if (config_.skip_check_sat()) {
    DLINEAR_DEBUG("ContextImpl::CheckOpt() - Skipping SAT check");
    UpdateAndPrintOutput(SmtResult::SKIP_SAT);
    return SmtResult::SKIP_SAT;
  }
  const SmtResult result = CheckOptCore(obj_lo, obj_up);
  if (SmtResult::DELTA_SAT == result || SmtResult::SAT == result) {
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
  UpdateAndPrintOutput(result);
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
  if (key == ":precision") config_.m_precision().SetFromFile(ParseDoubleOption(key, val));
  if (key == ":produce-models") return config_.m_produce_models().SetFromFile(ParseBooleanOption(key, val));
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

bool Context::Impl::IsModelVariable(const Variable &v) const { return model_variables_.contains(v.get_id()); }

void Context::Impl::MarkModelVariable(const Variable &v) { model_variables_.insert(v.get_id()); }

const ScopedVector<Formula> &Context::Impl::assertions() const { return stack_; }

bool Context::Impl::have_objective() const { return have_objective_; }

bool Context::Impl::is_max() const { return is_max_; }

[[nodiscard]] bool Context::Impl::Verify(const Box &model) const {
  Environment env;
  for (int i = 0; i < model.size(); i++) {
    const Variable &var = model.variable(i);
    const Interval &val = model.interval_vector()[i];
    DLINEAR_ASSERT(!val.is_empty(), "Variable cannot have an empty value interval");
    env.insert(var, val.ub());
  }
  for (const Formula &assertion : stack_) {
    if (!assertion.Evaluate(env)) {
      DLINEAR_ERROR_FMT("Not satisfied clause: {} - model {}", assertion, model);
      return false;
    }
  }
  return true;
}
void Context::Impl::Interrupt() {
  DLINEAR_DEBUG("ContextImpl::Interrupt()");
  interrupted_ = true;
}

SmtResult Context::Impl::CheckSatCore(mpq_class *actual_precision) {
  DLINEAR_DEBUG("ContextImpl::CheckSatCore()");
  DLINEAR_TRACE_FMT("ContextImpl::CheckSat: Box =\n{}", box());

  // If false ∈ stack, it's UNSAT.
  if (std::any_of(stack_.begin(), stack_.end(), drake::symbolic::is_false)) {
    DLINEAR_DEBUG("ContextImpl::CheckSat: Found false assertion");
    return SmtResult::UNSAT;
  }
  // If stack = ∅ or stack = {true}, it's trivially SAT.
  if (std::all_of(stack_.begin(), stack_.end(), drake::symbolic::is_true)) {
    DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - Found Model\n{}", box());
    return SmtResult::SAT;
  }

  //  DLINEAR_DEV_FMT("STATE: {}", fmt::join(assertions(), "\n"));

  // Add the theory literals from the SAT solver to the theory solver.
  theory_solver_->AddLiterals();
  // Consolidate the theory literals. No more literals can be added after this.
  theory_solver_->Consolidate(box());
  // See if any of the current literals can be used to guide the SAT by propagating and implying other literals.
  theory_solver_->Propagate(assert_cb_);

#ifndef NDEBUG
  if (debug_theory_solver != nullptr) {
    debug_theory_solver->AddLiterals();
    debug_theory_solver->Consolidate(box());
  }
#endif

  // Preprocess the fixed theory literals to avoid having to preprocess them again and again.
  DLINEAR_TRACE_FMT("Fixed theory literals: {}", sat_solver_->FixedTheoryLiterals());
  const bool success = theory_solver_->PreprocessFixedLiterals(sat_solver_->FixedTheoryLiterals(), conflict_cb_);
  if (!success) {
    DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Fixed bound check = UNSAT");
    return SmtResult::UNSAT;
  }

#if 0
  DLINEAR_DEV("Start tightening bounds");
  // Check the current constraints to see if there is anything that could be used to use for the guided constraints
  for (const std::unique_ptr<PiecewiseLinearConstraint> &constraint : pl_constraints_) {
    const std::set<LiteralSet> tight_explanations{constraint->TightenBounds(theory_solver_->m_fixed_preprocessor())};
    DLINEAR_DEV_TRACE_FMT("Tighten Bounds: {} - {}", constraint->theory_var(), *constraint);
    if (tight_explanations.empty()) continue;
    DLINEAR_DEV_DEBUG("ContextImpl::CheckSatCore() - Tightening bounds check = UNSAT");
    LearnExplanations(tight_explanations);
    return SmtResult::UNSAT;
  }
  theory_solver_->Backtrack();

  for (auto it = pl_constraints_.begin(); it != pl_constraints_.end();) {
    const LiteralSet learned_clauses{it->get()->LearnedClauses()};
    for (const Literal &learned_clause : learned_clauses) sat_solver_->AddLearnedClause(learned_clause);

#ifndef NDEBUG
    const Variable &var = it->get()->theory_var();
    const auto &bound = theory_solver_->fixed_theory_bounds().at(var);
    fmt::println("Fixed Bounds: {} = [{}, {}]", var, bound.active_lower_bound().get_d(),
                 bound.active_upper_bound().get_d());
#endif
    it = learned_clauses.empty() ? std::next(it) : pl_constraints_.erase(it);
  }

  if (!config_.onnx_file().empty()) {
    auto &nnSoplexTheorySolver = static_cast<NNSoplexTheorySolver &>(*theory_solver_);
    nnSoplexTheorySolver.SetPiecewiseLinearConstraints(pl_constraints_);
  }
#endif

  bool have_unsolved = false;
  while (!interrupted_) {
    // Note that 'DLINEAR_PYDLINEAR' is only defined in setup.py, when we build dlinear python package.
#ifdef DLINEAR_PYDLINEAR
    py_check_signals();
#endif

    DLINEAR_DEV_DEBUG("New iteration");
    // The box is passed in to the SAT solver solely to provide the LP solver
    // with initial bounds on the numerical variables.
    Model sat_model;
    const SatResult sat_result = sat_solver_->CheckSat(sat_model);

    // The SAT solver did not return a model.
    switch (sat_result) {
      case SatResult::DELTA_SAT:  // A SAT model was found. It is time to check the theory.
      case SatResult::SAT:
        break;
      case SatResult::UNSAT:
        if (have_unsolved) {  // There was an unsolved theory instance. The SMT solver failed to prove UNSAT.
          DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Sat Check = ERROR");
          return SmtResult::ERROR;
        } else {  // There is no unsolved theory instance. The SAT solver succeeded in proving UNSAT.
          DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Sat Check = UNSAT");
          return SmtResult::UNSAT;
        }
      case SatResult::ERROR:
        DLINEAR_ERROR("ContextImpl::CheckSatCore() - Sat Check = ERROR");
        return SmtResult::ERROR;
      default:
        DLINEAR_UNREACHABLE();
    }

    // The SAT solver found a model that satisfies the formula. SAT from SAT Solver.
    DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Sat Check = SAT");

    // Extrapolate the theory model from the SAT model.
    const std::vector<Literal> &theory_model{sat_model.theory_model};
    // If there is no theory to solve, the SAT solver output is enough to return SAT.
    if (theory_model.empty()) return SmtResult::SAT;

    theory_solver_->Backtrack();
    const bool enable_literals_success = theory_solver_->EnableLiterals(theory_model, conflict_cb_);
    if (!enable_literals_success) {
      DLINEAR_DEBUG("ContextImpl::CheckSatCore() - EnableLiterals = UNSAT");
      continue;
    }

    // If the SAT solver found a model, we have to check if it is consistent with the theory
    const TheoryResult theory_result = theory_solver_->CheckSat(actual_precision, conflict_cb_);
    if (theory_result == TheoryResult::DELTA_SAT || theory_result == TheoryResult::SAT) {
      // SAT from TheorySolver.
      DLINEAR_DEBUG_FMT("ContextImpl::CheckSatCore() - Theory CheckSat = {}", theory_result);
      box() = theory_solver_->model();
      // Update the Boolean variables in the model (not used by the LP solver).
      for (const auto &[var, truth] : sat_model.boolean_model) {
        box()[var] = truth ? 1 : 0;  // true -> 1 and false -> 0
      }
      return theory_result == TheoryResult::DELTA_SAT ? SmtResult::DELTA_SAT : SmtResult::SAT;
    }

    if (theory_result == TheoryResult::UNSAT) {  // UNSAT from TheorySolver.
      DLINEAR_DEBUG("ContextImpl::CheckSatCore() - Theory CheckSat = UNSAT");
    } else {
      DLINEAR_ASSERT(theory_result == TheoryResult::ERROR, "theory must be unsolved");
      DLINEAR_WARN("ContextImpl::CheckSatCore() - Theory CheckSat = UNKNOWN");
      LearnExplanation(LiteralSet{theory_model.begin(), theory_model.end()});
      have_unsolved = true;  // Will prevent return of UNSAT
    }
  }
  return SmtResult::TIMEOUT;
}

SmtResult Context::Impl::CheckOptCore([[maybe_unused]] mpq_class *obj_lo, [[maybe_unused]] mpq_class *obj_up) {
  DLINEAR_RUNTIME_ERROR("CheckOptCore() Not implemented");
}
void Context::Impl::MinimizeCore([[maybe_unused]] const Expression &obj_expr) {
  DLINEAR_RUNTIME_ERROR("MinimizeCore() Not implemented");
}
std::unique_ptr<TheorySolver> Context::Impl::GetTheorySolver() {
  switch (logic_.value_or(Logic::QF_LRA)) {
    case Logic::QF_LRA:
      if (config_.complete()) return std::make_unique<CompleteLpTheorySolver>(predicate_abstractor_);
      return std::make_unique<DeltaLpTheorySolver>(predicate_abstractor_);
    default:
      DLINEAR_RUNTIME_ERROR_FMT("Unsupported logic: {}", logic_.value());
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
  DLINEAR_DEV_FMT("ContextImpl::LearnExplanation({})", explanation);
  DLINEAR_ASSERT_FMT(!explanations_so_far.contains(explanation), "Explanation already present, looping!\n{}\nin\n{}",
                     explanation, explanations_so_far);
  DLINEAR_ASSERT(!explanation.empty(), "No explanation is provided. Infinite loop detected.");
#ifndef NDEBUG
  if (debug_theory_solver != nullptr) {
    debug_theory_solver->Backtrack();
    bool result = true;
    for (const Literal &lit : explanation) result &= debug_theory_solver->EnableLiteral(lit, debug_conflict_cb);
    if (result) {
      mpq_class precision{config_.precision()};
      const TheoryResult theory_result = debug_theory_solver->CheckSat(&precision, debug_conflict_cb);
      DLINEAR_ASSERT(theory_result == TheoryResult::UNSAT || theory_result == TheoryResult::ERROR,
                     "Explanation must be UNSAT or error");
    }
  }
  explanations_so_far.insert(explanation);
#endif
  sat_solver_->AddLearnedClause(explanation);
}

void Context::Impl::UpdateAndPrintOutput(const SmtResult smt_result) const {
  if (output_ == nullptr) return;
  DLINEAR_DEBUG("ContextImpl::UpdateAndPrintOutput() - Setting output");
  output_->result = smt_result;
  output_->n_assertions = assertions().size();
  if (config_.produce_models()) output_->model = model_;
  if (config_.verify()) output_->complete_model = box();
  if (config_.with_timings()) {
    DLINEAR_DEBUG("ContextImpl::UpdateAndPrintOutput() - Setting timings");
    output_->add_iteration_stats(sat_solver_->stats());
    output_->add_iteration_stats(theory_solver_->stats());
    output_->add_iteration_stats(ite_eliminator_.stats());
    output_->add_iteration_stats(predicate_abstractor_.stats());
    output_->add_iteration_stats(sat_solver_->cnfizer_stats());
    for (const auto &propagator : theory_solver_->propagators()) output_->add_iteration_stats(propagator->stats());
    for (const auto &preprocessor : theory_solver_->preprocessors())
      output_->add_iteration_stats(preprocessor->stats());
  }
  if (!config_.silent() && config_.csv()) {
    IterationStats preprocessors_total_stats{true, ""};
    for (const auto &preprocessor : theory_solver_->preprocessors()) preprocessors_total_stats += preprocessor->stats();
    std::cout << "file,complete,satSolver,lpSolver,assertions,precision,actualPrecision,simplexPhase,"
                 "simpleBoundPropagationFrequency,boundCheckingFrequency,satDefaultPhase,lpMode,"
                 "timeUnit,parserTime,satTime,preprocessorTime,theoryTime,smtTime,result\n";
    std::cout << config_.filename() << ","                            //
              << config_.complete() << ","                            //
              << config_.sat_solver() << ","                          //
              << config_.lp_solver() << ","                           //
              << output_->n_assertions << ","                         //
              << config_.precision() << ","                           //
              << output_->actual_precision.get_d() << ","             //
              << config_.simplex_sat_phase() << ","                   //
              << config_.simple_bound_propagation_step() << ","  //
              << config_.bound_preprocess_step() << ","            //
              << config_.sat_default_phase() << ","                   //
              << config_.actual_lp_mode() << ","                      //
              << "s" << ","                                           //
              << output_->parser_stats.timer().seconds() << ","       //
              << sat_solver_->stats().timer().seconds() << ","        //
              << preprocessors_total_stats.timer().seconds() << ","   //
              << theory_solver_->stats().timer().seconds() << ","     //
              << output_->smt_solver_timer.seconds() << ","           //
              << output_->result << std::endl;
  } else if (!config_.silent()) {
    std::cout << *output_ << std::endl;
  }
}

}  // namespace dlinear
