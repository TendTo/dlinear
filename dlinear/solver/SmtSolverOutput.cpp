/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "SmtSolverOutput.h"

#include <cmath>
#include <limits>
#include <sstream>

#include "dlinear/util/exception.h"

namespace dlinear {

SmtResult parse_smt_result(const SatResult sat_result) {
  switch (sat_result) {
    case SatResult::SAT_SATISFIABLE:
      return SmtResult::SAT;
    case SatResult::SAT_DELTA_SATISFIABLE:
      return SmtResult::DELTA_SAT;
    case SatResult::SAT_UNSATISFIABLE:
      return SmtResult::UNSAT;
    case SatResult::SAT_UNSOLVED:
      return SmtResult::UNKNOWN;
    case SatResult::SAT_NO_RESULT:
      return SmtResult::UNSOLVED;
    default:
      DLINEAR_UNREACHABLE();
  }
}

SmtResult parse_smt_result(const LpResult lp_result) {
  switch (lp_result) {
    case LpResult::LP_OPTIMAL:
      return SmtResult::OPTIMAL;
    case LpResult::LP_DELTA_OPTIMAL:
      return SmtResult::DELTA_OPTIMAL;
    case LpResult::LP_UNBOUNDED:
      return SmtResult::UNBOUNDED;
    case LpResult::LP_INFEASIBLE:
      return SmtResult::INFEASIBLE;
    case LpResult::LP_UNSOLVED:
      return SmtResult::UNKNOWN;
    case LpResult::LP_NO_RESULT:
      return SmtResult::UNSOLVED;
    default:
      DLINEAR_UNREACHABLE();
  }
}

double SmtSolverOutput::precision_upper_bound() const {
  return std::nextafter(actual_precision.get_d(), std::numeric_limits<double>::infinity());
}

int SmtSolverOutput::exit_code() const {
  switch (result) {
    case SmtResult::SAT:
    case SmtResult::DELTA_SAT:
    case SmtResult::OPTIMAL:
    case SmtResult::DELTA_OPTIMAL:
    case SmtResult::UNBOUNDED:
      return 0;
    case SmtResult::UNSAT:
    case SmtResult::INFEASIBLE:
      return 1;
    case SmtResult::UNKNOWN:
      return 2;
    case SmtResult::ERROR:
      return 3;
    default:
      return 4;
  }
}

bool SmtSolverOutput::matches_expectation(SmtResult expectation) const {
  if (expectation == SmtResult::UNKNOWN) return true;
  if (expectation != SmtResult::SAT && expectation != SmtResult::UNSAT) DLINEAR_RUNTIME_ERROR("Invalid expectation");
  switch (result) {
    case SmtResult::SAT:
    case SmtResult::UNSAT:
      return result == expectation;
    case SmtResult::OPTIMAL:
    case SmtResult::UNBOUNDED:
      return expectation == SmtResult::SAT;
    case SmtResult::DELTA_SAT:
    case SmtResult::DELTA_OPTIMAL:
      return expectation == SmtResult::SAT || expectation == SmtResult::UNSAT;
    case SmtResult::INFEASIBLE:
      return expectation == SmtResult::UNSAT;
    case SmtResult::SKIP_SAT:
    case SmtResult::UNSOLVED:
      return true;
    case SmtResult::ERROR:
    case SmtResult::UNKNOWN:
      return false;
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream& operator<<(std::ostream& os, const SmtResult& bound) {
  switch (bound) {
    case SmtResult::UNSAT:
      return os << "unsat";
    case SmtResult::SKIP_SAT:
      return os << "skip-sat";
    case SmtResult::UNSOLVED:
      return os << "unsolved";
    case SmtResult::SAT:
      return os << "sat";
    case SmtResult::DELTA_SAT:
      return os << "delta-sat";
    case SmtResult::UNKNOWN:
      return os << "unknown";
    case SmtResult::ERROR:
      return os << "error";
    case SmtResult::OPTIMAL:
      return os << "optimal";
    case SmtResult::DELTA_OPTIMAL:
      return os << "delta-optimal";
    case SmtResult::UNBOUNDED:
      return os << "unbounded";
    case SmtResult::INFEASIBLE:
      return os << "infeasible";
    default:
      DLINEAR_UNREACHABLE();
  }
}

std::ostream& operator<<(std::ostream& os, const SmtSolverOutput& s) {
  switch (s.result) {
    case SmtResult::UNSOLVED:
      return os << "unsolved";
    case SmtResult::UNKNOWN:
      return os << "unknown";
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
    case SmtResult::OPTIMAL:
      os << "optimal with delta = 0, range = [" << s.lower_bound << ", " << s.upper_bound << "]";
      break;
    case SmtResult::DELTA_OPTIMAL: {
      mpq_class diff = s.upper_bound - s.lower_bound;
      os << "delta-optimal with delta = " << diff.get_d() << " ( = " << diff << "), range = [" << s.lower_bound << ", "
         << s.upper_bound << "]";
    } break;
    case SmtResult::UNBOUNDED:
      os << "unbounded";
      break;
    case SmtResult::INFEASIBLE:
      os << "infeasible";
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
