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
  if (output_.result() != SolverResult::UNSOLVED) return output_;
  ParseInput();
  CheckSatCore();
  return output_;
}

void Solver::ParseInput() {
  switch (config_.format()) {
    case Config::Format::AUTO:
      if (config_.read_from_stdin()) return ParseSmt2();
      if (config_.filename_extension() == "smt2") return ParseSmt2();
      if (config_.filename_extension() == "mps") return ParseMps();
      DLINEAR_UNREACHABLE();
    case Config::Format::SMT2:
      ParseSmt2();
      break;
    case Config::Format::MPS:
      ParseMps();
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
}

void Solver::ParseSmt2() {
  DLINEAR_TRACE("Solver::ParseSmt2");
  smt2::Smt2Driver smt2_driver{&context_};
  smt2_driver.set_trace_scanning(config_.debug_scanning());
  smt2_driver.set_trace_parsing(config_.debug_parsing());
  if (config_.read_from_stdin()) {
    smt2_driver.parse_stream(std::cin, "(stdin)");
  } else {
    smt2_driver.parse_file(config_.filename());
  }

  DLINEAR_TRACE("Solver::ParseSmt2 -- Finished parsing file.");
}

void Solver::ParseMps() {
  DLINEAR_TRACE("Solver::ParseMps");

  mps::MpsDriver mps_driver{&context_};
  mps_driver.set_debug_scanning(config_.debug_scanning());
  mps_driver.set_debug_parsing(config_.debug_parsing());
  if (config_.read_from_stdin()) {
    mps_driver.parse_stream(std::cin, "(stdin)");
  } else {
    mps_driver.parse_file(config_.filename());
  }

  DLINEAR_TRACE("Solver::ParseMps -- Finished parsing file.");
}

void Solver::CheckCore() {
  if (context_.have_objective())
    CheckObjCore();
  else
    CheckSatCore();
}

void Solver::CheckObjCore() {
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
  const tl::optional<Box> model{context_.CheckSat(&output_.mutable_actual_precision())};
  if (model) {
    output_.mutable_model() = *model;
    output_.mutable_result() = SolverResult::DELTA_SAT;
  } else {
    output_.mutable_result() = SolverResult::UNSAT;
  }
}

}  // namespace dlinear
