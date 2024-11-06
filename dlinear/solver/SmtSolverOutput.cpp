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
    default:
      return 3;
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
    default:
      DLINEAR_UNREACHABLE();
  }
  if (s.with_timings) {
    os << " after " << s.smt_solver_timer.seconds() << " seconds\n"
       << s.parser_stats << "\n"
       << s.ite_stats << "\n"
       << s.cnfizer_stats << "\n"
       << s.predicate_abstractor_stats << "\n"
       << s.preprocessor_stats << "\n"
       << s.sat_stats << "\n"
       << s.theory_stats;
  }
  if (!s.model.empty() && s.produce_models) {
    os << "\n" << s.model;
  }
  return os;
}

}  // namespace dlinear
