/**
 * @file Solver.cpp
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 */
#include "Solver.h"

#include <tl/optional.hpp>

#include "dlinear/mps/Driver.h"
#include "dlinear/smt2/Driver.h"
#include "dlinear/solver/SolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {
Solver::Solver() : Solver{Config{true}} {}
Solver::Solver(const std::string& filename) : Solver{Config{filename}} {}
Solver::Solver(const Config& config)
    : config_{config},
      guard_{config_},
      context_{config_},
      output_{config_.precision(), config_.produce_models(), config_.with_timings()} {}

SolverOutput Solver::CheckSat() {
  DLINEAR_TRACE("Solver::CheckSat");
  if (output_.result() != SolverResult::UNSOLVED) return output_;
  DLINEAR_DEBUG("Solver::CheckSat -- No previous result fond.");
  if (!ParseInput()) DLINEAR_RUNTIME_ERROR_FMT("Failed to parse input file: {}", config_.filename());
  output_.mutable_n_assertions() = context_.assertions().size();

  if (config_.skip_check_sat())
    output_.mutable_result() = SolverResult::SKIP_SAT;
  else
    CheckCore();

  return output_;
}

bool Solver::ParseInput() {
  DLINEAR_TRACE("Solver::ParseInput");
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
  return false;
}

bool Solver::ParseSmt2() {
  DLINEAR_DEBUG("Solver::ParseSmt2");
  smt2::Smt2Driver smt2_driver{&context_};
  if (config_.read_from_stdin()) return smt2_driver.parse_stream(std::cin, "(stdin)");
  return smt2_driver.parse_file(config_.filename());
}

bool Solver::ParseMps() {
  DLINEAR_DEBUG("Solver::ParseMps");
  mps::MpsDriver mps_driver{&context_};
  if (config_.read_from_stdin()) return mps_driver.parse_stream(std::cin, "(stdin)");
  return mps_driver.parse_file(config_.filename());
}

void Solver::CheckCore() {
  if (context_.have_objective())
    CheckObjCore();
  else
    CheckSatCore();
}

void Solver::CheckObjCore() {
  DLINEAR_DEBUG("Solver::CheckObjCore");
  int status =
      context_.CheckOpt(&output_.mutable_lower_bound(), &output_.mutable_upper_bound(), &output_.mutable_model());
  if (LP_DELTA_OPTIMAL == status) {
    output_.mutable_result() = SolverResult::DELTA_OPTIMAL;
  } else if (LP_UNBOUNDED == status) {
    output_.mutable_result() = SolverResult::UNBOUNDED;
  } else if (LP_INFEASIBLE == status) {
    output_.mutable_result() = SolverResult::UNFEASIBLE;
  } else {
    DLINEAR_UNREACHABLE();
  }
}

void Solver::CheckSatCore() {
  DLINEAR_DEBUG("Solver::CheckSatCore");
  const tl::optional<Box> model{context_.CheckSat(&output_.mutable_actual_precision())};
  if (model) {
    output_.mutable_model() = *model;
    output_.mutable_result() = SolverResult::DELTA_SAT;
  } else {
    output_.mutable_result() = SolverResult::UNSAT;
  }
}

}  // namespace dlinear
