/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SmtSolverOutput.h"

#include <cmath>
#include <limits>
#include <ostream>
#include <sstream>

#include "dlinear/util/error.h"

namespace dlinear {

double SmtSolverOutput::precision_upper_bound() const {
  return std::nextafter(actual_precision.get_d(), std::numeric_limits<double>::infinity());
}

int SmtSolverOutput::exit_code() const {
  switch (result) {
    case SmtResult::SKIP_SAT:
    case SmtResult::SAT:
    case SmtResult::DELTA_SAT:
      return 0;
    case SmtResult::UNSAT:
      return 1;
    case SmtResult::ERROR:
      return 2;
    case SmtResult::TIMEOUT:
      return 3;
    default:
      return 4;
  }
}

bool SmtSolverOutput::matches_expectation(SmtResult expectation) const {
  if (expectation == SmtResult::UNSOLVED) return true;
  if (expectation != SmtResult::SAT && expectation != SmtResult::UNSAT) DLINEAR_RUNTIME_ERROR("Invalid expectation");
  switch (result) {
    case SmtResult::SAT:
    case SmtResult::UNSAT:
      return result == expectation;
    case SmtResult::DELTA_SAT:
      return expectation == SmtResult::SAT || expectation == SmtResult::UNSAT;
    case SmtResult::SKIP_SAT:
    case SmtResult::UNSOLVED:
      return true;
    case SmtResult::ERROR:
    case SmtResult::TIMEOUT:
      return false;
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream& operator<<(std::ostream& os, const SmtSolverOutput& s) {
  switch (s.result) {
    case SmtResult::UNSOLVED:
      return os << "unsolved";
    case SmtResult::ERROR:
      return os << "error";
    case SmtResult::SAT:
      os << "sat";
      break;
    case SmtResult::DELTA_SAT:
      os << "delta-sat with delta = " << s.precision_upper_bound() << " ( > " << s.actual_precision << " )";
      break;
    case SmtResult::UNSAT:
      os << "unsat";
      break;
    case SmtResult::SKIP_SAT:
      os << "No satisfiability check was performed\n"
            "To use the SAT solver, remove the option --skip-check-sat\n"
            "skip-sat";
      break;
    case SmtResult::TIMEOUT:
      os << "timeout";
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  if (s.with_timings) {
    os << " after " << s.smt_solver_timer.seconds() << " seconds";
    os << "\n" << s.parser_stats;
    for (const IterationStats& stats : s.iteration_stats) {
      if (stats.iterations() > 0) os << "\n" << stats;
    }
  }
  if (!s.model.empty() && s.produce_models) {
    os << "\n" << s.model;
  }
  return os;
}

}  // namespace dlinear
