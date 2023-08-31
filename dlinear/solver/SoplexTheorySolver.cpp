/**
 * @file SoplexTheorySolver.cpp
 * @author dlinear
 * @date 24 Aug 2023
 * @copyright 2023 dlinear
 */

#include "SoplexTheorySolver.h"

#include "dlinear/solver/Context.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"

using std::cout;
using std::set;
using std::vector;
using std::pair;

using soplex::SoPlex;
using soplex::SPxSolver;
using soplex::VectorRational;
using soplex::LPColRational;
using soplex::Rational;

using dlinear::gmp::to_mpq_t;
using dlinear::gmp::to_mpq_class;

namespace dlinear {

SoplexTheorySolver::SoplexTheorySolver(const Config &config)
    : config_{config} {
}

namespace {
class TheorySolverStat : public Stats {
 public:
  explicit TheorySolverStat(const bool enabled) : Stats{enabled} {}
  TheorySolverStat(const TheorySolverStat &) = delete;
  TheorySolverStat(TheorySolverStat &&) = delete;
  TheorySolverStat &operator=(const TheorySolverStat &) = delete;
  TheorySolverStat &operator=(TheorySolverStat &&) = delete;
  ~TheorySolverStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of CheckSat",
            "Theory level", num_check_sat_);
      print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in CheckSat", "Theory level",
            timer_check_sat_.seconds());
    }
  }

  void increase_num_check_sat() { increase(&num_check_sat_); }

  Timer timer_check_sat_;

 private:
  std::atomic<int> num_check_sat_{0};
};

}  // namespace

int SoplexTheorySolver::CheckSat(const Box &box,
                                 const std::vector<Literal> &assertions,
                                 SoPlex *prob,
                                 const VectorRational &lower,
                                 const VectorRational &upper,
                                 const std::map<int, Variable> &var_map) {
  DLINEAR_ASSERT(prob != nullptr, "Prob is null");
  static TheorySolverStat stat{DLINEAR_INFO_ENABLED};
  stat.increase_num_check_sat();
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, stat.enabled(), true /* start_timer */);

  DLINEAR_TRACE_FMT("SoplexTheorySolver::CheckSat: Box = \n{}", box);

  SPxSolver::Status status = SPxSolver::Status::UNKNOWN;
  int sat_status = SAT_NO_RESULT;

  precision_ = config_.precision();

  int rowcount = prob->numRowsRational();
  int colcount = prob->numColsRational();
  VectorRational x;

  model_ = box;
  for (const pair<const int, Variable> &kv : var_map) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("SoplexTheorySolver::CheckSat: Adding var {} to model from SAT", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to
  // handle that here.  Also, if there are no constraints, we can immediately
  // return SAT afterward if the bounds are OK.
  sat_status = SAT_DELTA_SATISFIABLE;
  for (const pair<const int, Variable> &kv : var_map) {
    const Rational &lb{lower[kv.first]};
    const Rational &ub{upper[kv.first]};
    if (lb > ub) {
      DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: variable {} has invalid bounds [{}, {}]", kv.second, lb, ub);
      sat_status = SAT_UNSATISFIABLE;
      // Prevent the exact same LP from coming up again
      explanation_.clear();
      explanation_.insert(assertions.begin(), assertions.end());
      break;
    }
    if (rowcount == 0) {
      Rational val;
      if (-soplex::infinity < lb) {
        val = lb;
      } else if (ub < soplex::infinity) {
        val = ub;
      } else {
        val = 0;
      }
      DLINEAR_ASSERT(to_mpq_t(model_[kv.second].lb()) <= val && val <= to_mpq_t(model_[kv.second].ub()),
                     "val must be in bounds");
      model_[kv.second] = val.backend().data();
    }
  }
  if (sat_status == SAT_UNSATISFIABLE || rowcount == 0) {
    DLINEAR_DEBUG("SoplexTheorySolver::CheckSat: no need to call LP solver");
    return sat_status;
  }

  prob->changeLowerRational(lower);
  prob->changeUpperRational(upper);

  // Now we call the solver
  sat_status = SAT_UNSOLVED;
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: calling SoPlex (phase {})",
                    1 == config_.simplex_sat_phase() ? "one" : "two");

  mpq_class actual_precision{precision_};
  status = prob->optimize();
  actual_precision = 0;  // Because we always solve exactly, at present

  if ((2 == config_.simplex_sat_phase() && status != SPxSolver::Status::OPTIMAL) ||
      (status != SPxSolver::Status::OPTIMAL &&
          status != SPxSolver::Status::UNBOUNDED &&
          status != SPxSolver::Status::INFEASIBLE)) {
    DLINEAR_RUNTIME_ERROR_FMT("SoPlex returned {}", status);
  } else {
    DLINEAR_DEBUG_FMT("SoplexTheorySolver::CheckSat: SoPlex has returned with precision = {}", actual_precision);
  }

  x.reDim(colcount);
  bool haveSoln = prob->getPrimalRational(x);
  if (haveSoln && x.dim() != colcount) {
    DLINEAR_ASSERT(x.dim() >= colcount, "x.dim() must be > colcount");
    DLINEAR_WARN_FMT("SoplexTheorySolver::CheckSat: colcount = {} but x.dim() = {} after getPrimalRational()",
                     colcount,
                     x.dim());
  }
  DLINEAR_ASSERT(status != SPxSolver::Status::OPTIMAL || haveSoln, "status must be OPTIMAL or haveSoln must be true");

  if (1 == config_.simplex_sat_phase()) {
    switch (status) {
      case SPxSolver::Status::OPTIMAL:
      case SPxSolver::Status::UNBOUNDED:sat_status = SAT_DELTA_SATISFIABLE;
        break;
      case SPxSolver::Status::INFEASIBLE:sat_status = SAT_UNSATISFIABLE;
        break;
        //case QS_LP_UNSOLVED:
        //  sat_status = SAT_UNSOLVED;
        //  break;
      default:DLINEAR_UNREACHABLE();
    }
  } else {
    // The feasibility LP should always be feasible & bounded
    DLINEAR_ASSERT(status == SPxSolver::Status::OPTIMAL, "status must be OPTIMAL");
    VectorRational obj;
    prob->getObjRational(obj);
    DLINEAR_ASSERT(obj.dim() == colcount, "obj.dim() must be == colcount");
    bool ok = true;
    // ok = std::ranges::all_of(0, colcount, [&] (int i) { return obj[i] == 0 || x[i] == 0; });
    for (int i = 0; i < colcount; ++i) {
      if (!(ok = (obj[i] == 0 || x[i] == 0))) {
        break;
      }
    }
    if (ok) {
      sat_status = SAT_DELTA_SATISFIABLE;
    } else {
      sat_status = SAT_UNSATISFIABLE;
    }
  }

  if (sat_status == SAT_UNSOLVED) {
    DLINEAR_DEBUG("SoplexTheorySolver::CheckSat: SoPlex failed to return a result");
  }

  switch (sat_status) {
    case SAT_DELTA_SATISFIABLE:
      if (haveSoln) {
        // Copy delta-feasible point from x into model_
        for (const pair<const int, Variable> &kv : var_map) {
          DLINEAR_ASSERT(model_[kv.second].lb() <= to_mpq_class(x[kv.first].backend().data())
                             && to_mpq_class(x[kv.first].backend().data()) <= model_[kv.second].ub(),
                         "val must be in bounds");
          model_[kv.second] = x[kv.first].backend().data();
        }
      } else {
        DLINEAR_RUNTIME_ERROR("delta-sat but no solution available");
      }
      break;
    case SAT_UNSATISFIABLE:
    case SAT_UNSOLVED:
      // Prevent the exact same LP from coming up again
      explanation_.clear();
      explanation_.insert(assertions.begin(), assertions.end());
      break;
    default:DLINEAR_UNREACHABLE();
  }

  return sat_status;
}

const Box &SoplexTheorySolver::GetModel() const {
  DLINEAR_DEBUG_FMT("SoplexTheorySolver::GetModel():\n{}", model_);
  return model_;
}

const LiteralSet &SoplexTheorySolver::GetExplanation() const {
  return explanation_;
}

} // namespace dlinear
