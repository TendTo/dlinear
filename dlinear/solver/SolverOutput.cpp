/**
 * @file SolverOutput.cpp
 * @author dlinear
 * @date 16 Sep 2023
 * @copyright 2023 dlinear
 */

#include "SolverOutput.h"

#include <limits>
#include <sstream>

#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"

namespace dlinear {

double SolverOutput::precision_upper_bound() const {
  return nextafter(actual_precision_.get_d(), std::numeric_limits<double>::infinity());
}

std::string SolverOutput::ToString() const {
  std::ostringstream oss;
  oss << *this;
  return oss.str();
}

std::ostream& operator<<(std::ostream& os, const SolverResult& bound) {
  switch (bound) {
    case SolverResult::UNSAT:
      return os << "unsat";
    case SolverResult::SKIP_SAT:
      return os << "skip-sat";
    case SolverResult::UNSOLVED:
      return os << "unsolved";
    case SolverResult::SAT:
      return os << "sat";
    case SolverResult::DELTA_SAT:
      return os << "delta-sat";
    case SolverResult::UNKNOWN:
      return os << "unknown";
    case SolverResult::ERROR:
      return os << "error";
    case SolverResult::OPTIMAL:
      return os << "optimal";
    case SolverResult::DELTA_OPTIMAL:
      return os << "delta-optimal";
    case SolverResult::UNBOUNDED:
      return os << "unbounded";
    case SolverResult::UNFEASIBLE:
      return os << "unfeasible";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream& operator<<(std::ostream& os, const SolverOutput& s) {
  switch (s.result()) {
    case SolverResult::UNSOLVED:
      return os << "unsolved";
    case SolverResult::UNKNOWN:
      return os << "unknown";
    case SolverResult::ERROR:
      return os << "error";
    case SolverResult::SAT:
    case SolverResult::DELTA_SAT:
      os << fmt::format("delta-sat with delta = {} ( > {})", s.precision_upper_bound(), s.actual_precision());
      break;
    case SolverResult::UNSAT:
      os << "unsat";
      break;
    case SolverResult::OPTIMAL:
    case SolverResult::DELTA_OPTIMAL: {
      mpq_class diff = s.upper_bound() - s.lower_bound();
      os << fmt::format("delta-optimal with delta = {} ( = {}), range = [{}, {}]", diff.get_d(), diff, s.lower_bound(),
                        s.upper_bound());
    } break;
    case SolverResult::UNBOUNDED:
      os << "unbounded";
      break;
    case SolverResult::UNFEASIBLE:
      os << "unfeasible";
      break;
    case SolverResult::SKIP_SAT:
      os << "skip-sat\n"
            "No satisfiability check was performed\n"
            "To use the SAT solver, remove the option --skip-check-sat";
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  if (s.with_timings()) {
    os << fmt::format(" after {} seconds", main_timer.seconds());
  }
  if (!s.model().empty() && s.produce_models()) {
    os << "\n";
    os << fmt::format("{}", s.model());
  }
  return os;
}

}  // namespace dlinear
