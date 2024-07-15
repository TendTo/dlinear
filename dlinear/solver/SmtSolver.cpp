/**
 * @file SmtSolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SmtSolver.h"

#include <iostream>
#include <utility>

#include "dlinear/parser/mps/Driver.h"
#include "dlinear/parser/onnx/Driver.h"
#include "dlinear/parser/smt2/Driver.h"
#include "dlinear/parser/vnnlib/Driver.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/OptionValue.hpp"
#include "dlinear/util/Timer.h"
#include "dlinear/util/concepts.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

namespace {
template <IsAnyOf<smt2::Smt2Driver, mps::MpsDriver, onnx::OnnxDriver, vnnlib::VnnlibDriver> T>
inline bool ParseInputCore(const Config &config, Context &context) {
  DLINEAR_DEBUG("SmtSolver::ParseSmt2");
  T driver{context};
  return config.read_from_stdin() ? driver.ParseStream(std::cin, "(stdin)") : driver.ParseFile(config.filename());
}

template <>
inline bool ParseInputCore<onnx::OnnxDriver>(const Config &config, Context &context) {
  DLINEAR_DEBUG("SmtSolver::ParseOnnx");
  onnx::OnnxDriver driver{context};
  return driver.ParseFile(config.onnx_file());
}
}  // namespace

SmtSolver::SmtSolver(const std::string &filename) : SmtSolver{Config{filename}} {}
SmtSolver::SmtSolver(Config config) : config_{std::move(config)}, output_{config_}, context_{config_, &output_} {}

#ifdef DLINEAR_PYDLINEAR
SmtSolver &SmtSolver::Enter() { return *this; }

void SmtSolver::Exit() { guard_.DeInit(); }
#endif

const SmtSolverOutput &SmtSolver::CheckSat() {
  DLINEAR_TRACE("SmtSolver::CheckSat");
  TimerGuard timer_guard{&output_.total_timer, true};

  if (config_.skip_check_sat()) {
    output_.result = SmtResult::SKIP_SAT;
    return output_;
  }

  if (context_.have_objective())
    context_.CheckOpt(&output_.lower_bound, &output_.upper_bound);
  else
    context_.CheckSat(&output_.actual_precision);

  return output_;
}

const SmtSolverOutput &SmtSolver::Parse(const std::string &filename) {
  config_.m_filename() = filename;
  config_.m_read_from_stdin() = filename.empty();
  return Parse();
}
const SmtSolverOutput &SmtSolver::Parse() {
  DLINEAR_TRACE("SmtSolver::Parse");

  if (!ParseInput()) DLINEAR_RUNTIME_ERROR("Error parsing the input");
  return output_;
}

std::string SmtSolver::GetInfo(const std::string &key) const { return context_.GetInfo(key); }
std::string SmtSolver::GetOption(const std::string &key) const { return context_.GetOption(key); }
SmtResult SmtSolver::GetExpected() const {
  std::string status = context_.GetInfo(":status");
  if (status == "sat") return SmtResult::SAT;
  if (status == "unsat") return SmtResult::UNSAT;
  return SmtResult::UNKNOWN;
}

void SmtSolver::Assert(const Formula &f) {
  DLINEAR_TRACE_FMT("SmtSolver::Assert: {}", f);
  output_.result = SmtResult::UNSOLVED;
  context_.Assert(f);
}
bool SmtSolver::ParseInput() {
  DLINEAR_TRACE("SmtSolver::ParseInput");
  if (!config_.read_from_stdin() && config_.filename().empty()) {
    DLINEAR_INFO("SmtSolver::ParseInput: No input file provided");
    return true;
  } else if (config_.read_from_stdin() && config_.filename().empty()) {
    DLINEAR_INFO("SmtSolver::ParseInput: Reading from stdin");
  } else {
    DLINEAR_INFO_FMT("SmtSolver::ParseInput: Reading from file: {}", config_.filename());
  }
  TimerGuard timer_guard{&output_.total_timer, true};

  switch (config_.format()) {
    case Config::Format::AUTO:
      if (config_.read_from_stdin()) DLINEAR_RUNTIME_ERROR("Cannot determine format from stdin");
      if (config_.filename_extension() == "smt2") return ParseInputCore<smt2::Smt2Driver>(config_, context_);
      if (config_.filename_extension() == "mps") return ParseInputCore<mps::MpsDriver>(config_, context_);
      if (config_.filename_extension() == "vnnlib") {
        if (!ParseInputCore<onnx::OnnxDriver>(config_, context_)) return false;
        return ParseInputCore<vnnlib::VnnlibDriver>(config_, context_);
      }
      DLINEAR_UNREACHABLE();
    case Config::Format::SMT2:
      return ParseInputCore<smt2::Smt2Driver>(config_, context_);
    case Config::Format::MPS:
      return ParseInputCore<mps::MpsDriver>(config_, context_);
    case Config::Format::VNNLIB:
      if (!ParseInputCore<onnx::OnnxDriver>(config_, context_)) return false;
      return ParseInputCore<vnnlib::VnnlibDriver>(config_, context_);
    default:
      DLINEAR_UNREACHABLE();
  }
}

}  // namespace dlinear
