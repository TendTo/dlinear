/**
 * @file SmtSolverOutput.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SmtSolverOutput.h"

#include <spdlog/fmt/fmt.h>
#include <spdlog/fmt/ostr.h>

#include <limits>
#include <sstream>

#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

double SmtSolverOutput::precision_upper_bound() const {
  return nextafter(actual_precision.get_d(), std::numeric_limits<double>::infinity());
}

std::string SmtSolverOutput::ToString() const {
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
    case SolverResult::INFEASIBLE:
      return os << "infeasible";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream& operator<<(std::ostream& os, const SmtSolverOutput& s) {
  switch (s.result) {
    case SolverResult::UNSOLVED:
      return os << "unsolved";
    case SolverResult::UNKNOWN:
      return os << "unknown";
    case SolverResult::ERROR:
      return os << "error";
    case SolverResult::SAT:
      os << "sat with delta = 0";
      break;
    case SolverResult::DELTA_SAT:
      os << fmt::format("delta-sat with delta = {} ( > {})", s.precision_upper_bound(), s.actual_precision);
      break;
    case SolverResult::UNSAT:
      os << "unsat";
      break;
    case SolverResult::OPTIMAL:
      os << fmt::format("optimal with delta = 0, range = [{}, {}]", s.lower_bound, s.upper_bound);
      break;
    case SolverResult::DELTA_OPTIMAL: {
      mpq_class diff = s.upper_bound - s.lower_bound;
      os << fmt::format("delta-optimal with delta = {} ( = {}), range = [{}, {}]", diff.get_d(), diff, s.lower_bound,
                        s.upper_bound);
    } break;
    case SolverResult::UNBOUNDED:
      os << "unbounded";
      break;
    case SolverResult::INFEASIBLE:
      os << "infeasible";
      break;
    case SolverResult::SKIP_SAT:
      os << "skip-sat\n"
            "No satisfiability check was performed\n"
            "To use the SAT solver, remove the option --skip-check-sat";
      break;
    default:
      DLINEAR_UNREACHABLE();
  }
  if (s.with_timings) {
    os << fmt::format(" after {} seconds", main_timer.seconds());
  }
  if (!s.model.empty() && s.produce_models) {
    os << "\n";
    os << fmt::format("{}", s.model);
  }
  return os;
}

}  // namespace dlinear
