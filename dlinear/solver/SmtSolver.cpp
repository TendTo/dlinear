/**
 * @file SmtSolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SmtSolver.h"

#include <optional>
#include <utility>

#include "dlinear/mps/Driver.h"
#include "dlinear/smt2/Driver.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/concepts.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

namespace {
template <IsAnyOf<smt2::Smt2Driver, mps::MpsDriver> T>
inline bool ParseInputCore(const Config::ConstSharedConfig &config, Context &context, SmtSolverOutput &output) {
  DLINEAR_DEBUG("SmtSolver::ParseSmt2");
  T driver{context};
  const bool res =
      config->read_from_stdin() ? driver.parse_stream(std::cin, "(stdin)") : driver.parse_file(config->filename());
  if (config->with_timings() && res) output.parser_stats = driver.stats();
  return res;
}
}  // namespace

SmtSolver::SmtSolver() : SmtSolver{std::make_shared<Config>()} {}
SmtSolver::SmtSolver(const std::string &filename) : SmtSolver{std::make_shared<Config>(filename)} {}
SmtSolver::SmtSolver(const Config &config) : SmtSolver{std::make_shared<Config>(config)} {}
SmtSolver::SmtSolver(Config::SharedConfig config)
    : config_{std::move(config)}, guard_{*config_}, context_{config_}, output_{*config_} {}

#ifdef DLINEAR_PYDLINEAR

SmtSolver &SmtSolver::Enter() { return *this; }

void SmtSolver::Exit() { guard_.DeInit(); }

#endif

SmtSolverOutput SmtSolver::CheckSat() {
  DLINEAR_TRACE("SmtSolver::CheckSat");
  if (output_.result != SolverResult::UNSOLVED) return output_;
  TimerGuard timer_guard{&output_.total_timer, true};
  DLINEAR_DEBUG("SmtSolver::CheckSat: No cached result fond.");
  DLINEAR_INFO_FMT("SmtSolver::CheckSat: Checking satisfiability of '{}'", config_->filename());
  dlinear::main_timer.start();
  if (!ParseInput()) DLINEAR_RUNTIME_ERROR_FMT("Failed to parse input file: {}", config_->filename());
  output_.n_assertions = context_.assertions().size();

  if (config_->skip_check_sat())
    output_.result = SolverResult::SKIP_SAT;
  else if (context_.have_objective())
    CheckObjCore();
  else
    CheckSatCore();

  output_.model = context_.model();
  // Store stats
  if (config_->with_timings()) {
    const auto [predicate_abstractor_stats, cnfizer_stats, ite_stats] = context_.formula_visitors_stats();
    output_.predicate_abstractor_stats = predicate_abstractor_stats;
    output_.cnfizer_stats = cnfizer_stats;
    output_.ite_stats = ite_stats;
    output_.sat_stats = context_.sat_stats();
    output_.theory_stats = context_.theory_stats();
  }

  return output_;
}

bool SmtSolver::ParseInput() {
  DLINEAR_TRACE("SmtSolver::ParseInput");
  switch (config_->format()) {
    case Config::Format::AUTO:
      if (config_->read_from_stdin()) DLINEAR_RUNTIME_ERROR("Cannot determine format from stdin");
      if (config_->filename_extension() == "smt2") return ParseInputCore<smt2::Smt2Driver>(config_, context_, output_);
      if (config_->filename_extension() == "mps") return ParseInputCore<mps::MpsDriver>(config_, context_, output_);
      DLINEAR_UNREACHABLE();
    case Config::Format::SMT2:
      return ParseInputCore<smt2::Smt2Driver>(config_, context_, output_);
    case Config::Format::MPS:
      return ParseInputCore<mps::MpsDriver>(config_, context_, output_);
    default:
      DLINEAR_UNREACHABLE();
  }
}

void SmtSolver::CheckObjCore() {
  DLINEAR_DEBUG("SmtSolver::CheckObjCore");
  TimerGuard timer_guard{&output_.smt_solver_timer, true};
  const LpResult res = context_.CheckOpt(&output_.lower_bound, &output_.upper_bound);
  switch (res) {
    case LpResult::LP_DELTA_OPTIMAL:
      output_.result = SolverResult::DELTA_OPTIMAL;
      break;
    case LpResult::LP_UNBOUNDED:
      output_.result = SolverResult::UNBOUNDED;
      break;
    case LpResult::LP_INFEASIBLE:
      output_.result = SolverResult::INFEASIBLE;
      break;
    default:
      output_.result = SolverResult::UNKNOWN;
  }
}

void SmtSolver::CheckSatCore() {
  DLINEAR_DEBUG("SmtSolver::CheckSatCore");
  TimerGuard timer_guard{&output_.smt_solver_timer, true};
  const SatResult res = context_.CheckSat(&output_.actual_precision);
  switch (res) {
    case SatResult::SAT_SATISFIABLE:
      output_.result = SolverResult::SAT;
      break;
    case SatResult::SAT_DELTA_SATISFIABLE:
      output_.result = SolverResult::DELTA_SAT;
      break;
    case SatResult::SAT_UNSATISFIABLE:
      output_.result = SolverResult::UNSAT;
      break;
    default:
      output_.result = SolverResult::UNKNOWN;
  }
}
std::string SmtSolver::GetInfo(const std::string &key) const { return context_.GetInfo(key); }
std::string SmtSolver::GetOption(const std::string &key) const { return context_.GetOption(key); }
SolverResult SmtSolver::GetExpected() const {
  std::string status = context_.GetInfo(":status");
  if (status == "sat") return SolverResult::SAT;
  if (status == "unsat") return SolverResult::UNSAT;
  return SolverResult::UNKNOWN;
}

}  // namespace dlinear
