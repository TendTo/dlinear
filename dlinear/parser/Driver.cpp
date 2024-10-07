/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "Driver.h"

#include <fstream>
#include <iostream>
#include <sstream>  // IWYU pragma: keep for std::stringstream
#include <vector>

#include "dlinear/libs/libgmp.h"
#include "dlinear/solver/SmtSolverOutput.h"
#include "dlinear/symbolic/PrefixPrinter.h"
#include "dlinear/util/Box.h"
#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedVector.hpp"
#include "dlinear/util/exception.h"

namespace dlinear {

Driver::Driver(Context& context, const std::string& class_name)
    : context_{context},
      debug_scanning_{context_.config().debug_scanning()},
      debug_parsing_{context_.config().debug_parsing()},
      stats_{context.config().with_timings(), class_name, "Total time spent in parsing"},
      timer_{nullptr} {}

bool Driver::ParseStream(std::istream& in, const std::string& sname) {
  SmtSolverOutput* const output = context_.m_solver_output();
  // Decide whether to use the external output or the internal stats for the timer
  if (output != nullptr) {
    output->parser_stats = stats_;
    timer_ = &output->parser_stats.m_timer();
  } else {
    timer_ = &stats_.m_timer();
  }
  DLINEAR_ASSERT(timer_ != nullptr, "Timer must be set.");
  TimerGuard timer_guard(timer_, stats_.enabled());
  stream_name_ = sname;

  const bool res = ParseStreamCore(in);
  // If we used an external output as the timer, we need to update the internal stats
  if (output != nullptr) stats_ = output->parser_stats;
  return res;
}

bool Driver::ParseString(const std::string& input, const std::string& sname) {
  std::istringstream iss(input);
  return ParseStream(iss, sname);
}

bool Driver::ParseFile(const std::string& filename) {
  std::ifstream in(filename.c_str());
  if (!in.good()) return false;
  return ParseStream(in, filename);
}

void Driver::Error(const std::string& m) { std::cerr << m << std::endl; }

void Driver::CheckSat() {
  DLINEAR_ASSERT(timer_ != nullptr, "Timer must be set.");
  // Don't consider the time spent checking sat in the time spent parsing.
  timer_->pause();
  mpq_class precision = context_.config().precision();
  context_.CheckSat(&precision);
  timer_->resume();
}

void Driver::GetModel() {
  if (context_.config().silent()) return;
  std::cout << "(model\n" << context_.model() << "\n)" << std::endl;
}

void Driver::GetAssertions() const {
  if (context_.config().silent()) return;
  std::cout << "(assertions\n";
  for (const Formula& f : context_.assertions()) {
    std::stringstream ss;
    PrefixPrinter pp{ss};
    pp.Print(f);
    std::cout << "\t" << ss.str() << "\n";
  }
  std::cout << ")" << std::endl;
}

void Driver::GetOption(const std::string& key) const {
  if (context_.config().silent()) return;
  std::cout << "get-option ( " << key << " ): " << context_.GetOption(key) << std::endl;
}

void Driver::GetInfo(const std::string& key) const {
  if (context_.config().silent()) return;
  std::cout << "get-info ( " << key << " ): " << context_.GetInfo(key) << std::endl;
}

void Driver::Maximize(const Expression& f) {
  DLINEAR_ASSERT(timer_ != nullptr, "Timer must be set.");
  // Don't consider the time spent maximizing in the time spent parsing.
  timer_->pause();
  context_.Maximize(f);
  timer_->resume();
}

void Driver::Minimize(const Expression& f) {
  DLINEAR_ASSERT(timer_ != nullptr, "Timer must be set.");
  // Don't consider the time spent minimizing in the time spent parsing.
  timer_->pause();
  context_.Minimize(f);
  timer_->resume();
}

}  // namespace dlinear
