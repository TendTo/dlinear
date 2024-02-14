/**
 * @file Solver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "Solver.h"

#include <optional>
#include <utility>

#include "dlinear/mps/Driver.h"
#include "dlinear/smt2/Driver.h"
#include "dlinear/solver/SolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Infinity.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

Solver::Solver() : Solver{Config{true}} {}
Solver::Solver(const std::string &filename) : Solver{Config{filename}} {}
Solver::Solver(Config config)
    : config_{std::move(config)},
      guard_{config_},
      context_{config_},
      output_{config_.precision(), config_.produce_models(), config_.with_timings()} {}

#ifdef DLINEAR_PYDLINEAR

Solver &Solver::Enter() { return *this; }

void Solver::Exit() { guard_.DeInit(); }

#endif

SolverOutput Solver::CheckSat() {
  DLINEAR_TRACE("Solver::CheckSat");
  if (output_.result != SolverResult::UNSOLVED) return output_;
  DLINEAR_DEBUG("Solver::CheckSat -- No cached result fond.");
  if (!ParseInput()) DLINEAR_RUNTIME_ERROR_FMT("Failed to parse input file: {}", config_.filename());
  output_.n_assertions = context_.assertions().size();

  if (config_.skip_check_sat())
    output_.result = SolverResult::SKIP_SAT;
  else if (context_.have_objective())
    CheckObjCore();
  else
    CheckSatCore();

  return output_;
}

void Solver::Visualize() {
  DLINEAR_TRACE("Solver::Visualize");
  if (!ParseInput()) DLINEAR_RUNTIME_ERROR_FMT("Failed to parse input file: {}", config_.filename());
  for (const auto &a : context_.assertions()) std::cout << a << std::endl;
}

bool Solver::ParseInput() {
  DLINEAR_TRACE("Solver::ParseInput");
  TimerGuard timer_guard{&output_.parser_timer, true};
  switch (config_.format()) {
    case Config::Format::AUTO:
      if (config_.read_from_stdin()) return ParseSmt2();
      if (config_.filename_extension() == "smt2") return ParseSmt2();
      if (config_.filename_extension() == "mps") return ParseMps();
      DLINEAR_UNREACHABLE();
    case Config::Format::SMT2:
      return ParseSmt2();
    case Config::Format::MPS:
      return ParseMps();
    default:
      DLINEAR_UNREACHABLE();
  }
}

bool Solver::ParseSmt2() {
  DLINEAR_DEBUG("Solver::ParseSmt2");
  smt2::Smt2Driver smt2_driver{context_};
  if (config_.read_from_stdin()) return smt2_driver.parse_stream(std::cin, "(stdin)");
  return smt2_driver.parse_file(config_.filename());
}

bool Solver::ParseMps() {
  DLINEAR_DEBUG("Solver::ParseMps");
  mps::MpsDriver mps_driver{context_};
  if (config_.read_from_stdin()) return mps_driver.parse_stream(std::cin, "(stdin)");
  return mps_driver.parse_file(config_.filename());
}

void Solver::CheckObjCore() {
  DLINEAR_DEBUG("Solver::CheckObjCore");
  TimerGuard timer_guard{&output_.smt_solver_timer, true};
  LpResult status = context_.CheckOpt(&output_.lower_bound, &output_.upper_bound);
  if (LpResult::LP_DELTA_OPTIMAL == status) {
    output_.result = SolverResult::DELTA_OPTIMAL;
  } else if (LpResult::LP_UNBOUNDED == status) {
    output_.result = SolverResult::UNBOUNDED;
  } else if (LpResult::LP_INFEASIBLE == status) {
    output_.result = SolverResult::INFEASIBLE;
  } else {
    DLINEAR_UNREACHABLE();
  }
  output_.model = context_.model();
}

void Solver::CheckSatCore() {
  DLINEAR_DEBUG("Solver::CheckSatCore");
  TimerGuard timer_guard{&output_.smt_solver_timer, true};
  const SatResult res = context_.CheckSat(&output_.actual_precision);
  if (res == SatResult::SAT_SATISFIABLE) {
    output_.result = SolverResult::SAT;
  } else if (res == SatResult::SAT_DELTA_SATISFIABLE) {
    output_.result = SolverResult::DELTA_SAT;
  } else if (res == SatResult::SAT_UNSATISFIABLE) {
    output_.result = SolverResult::UNSAT;
  } else {
    output_.result = SolverResult::UNKNOWN;
  }
  output_.model = context_.model();
}
std::string Solver::GetInfo(const std::string &key) const { return context_.GetInfo(key); }
std::string Solver::GetOption(const std::string &key) const { return context_.GetOption(key); }
SolverResult Solver::GetExpected() const {
  std::string status = context_.GetOption(":status");
  if (status == "sat") return SolverResult::SAT;
  if (status == "unsat") return SolverResult::UNSAT;
  return SolverResult::UNKNOWN;
}

}  // namespace dlinear
