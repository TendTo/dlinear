/**
 * @file QsoptexTheorySolver.cpp
 * @author dlinear
 * @date 20 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#include "QsoptexTheorySolver.h"

using std::cout;
using std::endl;
using std::set;
using std::vector;
using std::pair;
using std::nextafter;
using std::numeric_limits;

using dlinear::qsopt_ex::MpqArray;
using dlinear::mpq_infty;
using dlinear::mpq_ninfty;

namespace dlinear {

QsoptexTheorySolver::QsoptexTheorySolver(const Config &config) : config_{config} {
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
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of CheckSat", "Theory level", num_check_sat_);
      print(cout,
            "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in CheckSat",
            "Theory level",
            timer_check_sat_.seconds());
    }
  }

  void increase_num_check_sat() { increase(&num_check_sat_); }

  Timer timer_check_sat_;

 private:
  std::atomic<int> num_check_sat_{0};
};

}  // namespace

int QsoptexTheorySolver::CheckOpt(const Box &box,
                                  mpq_class *obj_lo,
                                  mpq_class *obj_up,
                                  const std::vector<Literal> &assertions,
                                  const mpq_QSprob prob,
                                  const std::map<int, Variable> &var_map) {
  static TheorySolverStat stat{DLINEAR_INFO_ENABLED};
  stat.increase_num_check_sat();
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, stat.enabled(),
                                   true /* start_timer */);

  DLINEAR_TRACE_FMT("QsoptexTheorySolver::CheckOpt: Box = \n{}", box);

  int status = -1;
  int lp_status = LP_NO_RESULT;

  precision_ = config_.precision();

  size_t rowcount = mpq_QSget_rowcount(prob);
  size_t colcount = mpq_QSget_colcount(prob);

  // x: * must be allocated/deallocated using QSopt_ex.
  //    * should have room for the (rowcount) "logical" variables, which come
  //    after the (colcount) "structural" variables.
  MpqArray x{colcount + rowcount};
  MpqArray y{rowcount};
  MpqArray obj{colcount};
  mpq_QSget_obj(prob, static_cast<mpq_t *>(obj));

  model_ = box;
  for (const pair<const int, Variable> &kv : var_map) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("QsoptexTheorySolver::CheckOpt: Adding var {} to model from SAT", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to
  // handle that here.  Also, if there are no constraints, we can immediately
  // return SAT afterward if the bounds are OK.
  lp_status = LP_DELTA_OPTIMAL;
  mpq_t temp;
  mpq_init(temp);
  for (const pair<const int, Variable> &kv : var_map) {
    int res;
    res = mpq_QSget_bound(prob, kv.first, 'L', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class lb{temp};
    res = mpq_QSget_bound(prob, kv.first, 'U', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class ub{temp};
    if (lb > ub) {
      lp_status = LP_INFEASIBLE;
      // Prevent the exact same LP from coming up again
      explanation_.clear();
      explanation_.insert(assertions.begin(), assertions.end());
      break;
    }
    if (rowcount == 0) {
      mpq_class val;
      mpq_class obj_coef{obj[kv.first]};
      if (obj_coef > 0) {
        val = ub;
        if (ub >= mpq_infty()) {
          lp_status = LP_UNBOUNDED;
        }
      } else if (obj_coef < 0) {
        val = lb;
        if (lb <= mpq_ninfty()) {
          lp_status = LP_UNBOUNDED;
        }
      } else if (mpq_ninfty() < lb) {
        val = lb;
      } else if (ub < mpq_infty()) {
        val = ub;
      } else {
        val = 0;
      }
      DLINEAR_ASSERT(model_[kv.second].lb() <= val && val <= model_[kv.second].ub(), "Val must be in bounds");
      model_[kv.second] = val;
    }
  }
  mpq_clear(temp);
  if (lp_status == LP_INFEASIBLE || rowcount == 0) {
    DLINEAR_DEBUG("QsoptexTheorySolver::CheckOpt: no need to call LP solver");
    return lp_status;
  }

  // Now we call the solver
  int qs_lp_status = -1;
  DLINEAR_DEBUG("QsoptexTheorySolver::CheckOpt: calling QSopt_ex (full LP solver)");

  status = QSdelta_full_solver(prob, precision_.get_mpq_t(), static_cast<mpq_t *>(x), static_cast<mpq_t *>(y),
                               obj_lo->get_mpq_t(), obj_up->get_mpq_t(), NULL,
                               PRIMAL_SIMPLEX, &qs_lp_status, NULL, NULL);

  if (status) {
    DLINEAR_RUNTIME_ERROR_FMT("QSopt_ex returned {}", status);
  } else {
    // If QS_LP_DELTA_OPTIMAL, *obj_up and *obj_lo are valid bounds on the optimal objective.
    // Otherwise, *obj_up = *obj_lo = 0 and the result is exact.
    DLINEAR_DEBUG_FMT("QsoptexTheorySolver::CheckOpt: QSopt_ex has returned with precision = {}", *obj_up - *obj_lo);
  }

  if (QS_LP_UNSOLVED == qs_lp_status) {
    DLINEAR_DEBUG("QsoptexTheorySolver::CheckOpt: QSopt_ex failed to return a result");
  }

  lp_status = LP_NO_RESULT;

  switch (qs_lp_status) {
    case QS_LP_OPTIMAL:
    case QS_LP_DELTA_OPTIMAL:
      // Copy delta-optimal point from x into model_
      for (const pair<const int, Variable> &kv : var_map) {
        DLINEAR_ASSERT(
            model_[kv.second].lb() <= mpq_class(x[kv.first]) && mpq_class(x[kv.first]) <= model_[kv.second].ub(),
            "x[kv.first] must be in bounds");
        model_[kv.second] = x[kv.first];
      }
      lp_status = LP_DELTA_OPTIMAL;
      break;
    case QS_LP_INFEASIBLE:
      // Prevent the exact same LP from coming up again
      explanation_.clear();
      explanation_.insert(assertions.begin(), assertions.end());
      lp_status = LP_INFEASIBLE;
      break;
    case QS_LP_UNSOLVED:
      // Prevent the exact same LP from coming up again
      explanation_.clear();
      explanation_.insert(assertions.begin(), assertions.end());
      lp_status = LP_UNSOLVED;
      break;
    case QS_LP_UNBOUNDED:lp_status = LP_UNBOUNDED;
      break;
    case QS_LP_ITER_LIMIT:DLINEAR_RUNTIME_ERROR("Iteration limit reached");
    default:DLINEAR_RUNTIME_ERROR_FMT("QSopt_ex returned LP status {}", qs_lp_status);
  }

  return lp_status;
}

extern "C" void QsoptexCheckSatPartialSolution(mpq_QSdata const * /*prob*/,
                                               mpq_t *const /*x*/,
                                               const mpq_t infeas,
                                               const mpq_t /*delta*/,
                                               void *data) {
  auto *theory_solver = static_cast<QsoptexTheorySolver *>(data);
  // mpq_get_d() rounds towards 0.  This code guarantees infeas_gt > infeas.
  double infeas_gt = nextafter(mpq_get_d(infeas), numeric_limits<double>::infinity());
  // fmt::print uses shortest round-trip format for doubles, by default
  fmt::print("PARTIAL: delta-sat with delta = {} ( > {})",
             infeas_gt, mpq_class(infeas));
  if (theory_solver->config_.with_timings()) {
    fmt::print(" after {} seconds", main_timer.seconds());
  }
  fmt::print("\n");
}

int QsoptexTheorySolver::CheckSat(const Box &box,
                                  const std::vector<Literal> &assertions,
                                  const mpq_QSprob prob,
                                  const std::map<int, Variable> &var_map,
                                  mpq_class *actual_precision) {
  static TheorySolverStat stat{DLINEAR_INFO_ENABLED};
  stat.increase_num_check_sat();
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, stat.enabled(),
                                   true /* start_timer */);

  DLINEAR_TRACE_FMT("QsoptexTheorySolver::CheckSat: Box = \n{}", box);

  int status = -1;
  int sat_status = SAT_NO_RESULT;

  precision_ = config_.precision();

  size_t rowcount = mpq_QSget_rowcount(prob);
  size_t colcount = mpq_QSget_colcount(prob);
  // x: * must be allocated/deallocated using QSopt_ex.
  //    * should have room for the (rowcount) "logical" variables, which come
  //    after the (colcount) "structural" variables.
  MpqArray x{colcount + rowcount};

  model_ = box;
  for (const pair<const int, Variable> &kv : var_map) {
    if (!model_.has_variable(kv.second)) {
      // Variable should already be present
      DLINEAR_WARN_FMT("QsoptexTheorySolver::CheckSat: Adding var {} to model from SAT", kv.second);
      model_.Add(kv.second);
    }
  }

  // The solver can't handle problems with inverted bounds, so we need to
  // handle that here.  Also, if there are no constraints, we can immediately
  // return SAT afterward if the bounds are OK.
  sat_status = SAT_DELTA_SATISFIABLE;
  mpq_t temp;
  mpq_init(temp);
  for (const pair<const int, Variable> &kv : var_map) {
    int res;
    res = mpq_QSget_bound(prob, kv.first, 'L', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class lb{temp};
    res = mpq_QSget_bound(prob, kv.first, 'U', &temp);
    DLINEAR_ASSERT(!res, "Invalid res");
    mpq_class ub{temp};
    if (lb > ub) {
      sat_status = SAT_UNSATISFIABLE;
      // Prevent the exact same LP from coming up again
      explanation_.clear();
      explanation_.insert(assertions.begin(), assertions.end());
      break;
    }
    if (rowcount == 0) {
      mpq_class val;
      if (mpq_ninfty() < lb) {
        val = lb;
      } else if (ub < mpq_infty()) {
        val = ub;
      } else {
        val = 0;
      }
      DLINEAR_ASSERT(model_[kv.second].lb() <= val && val <= model_[kv.second].ub(), "Val must be in bounds");
      model_[kv.second] = val;
    }
  }
  mpq_clear(temp);
  if (sat_status == SAT_UNSATISFIABLE || rowcount == 0) {
    DLINEAR_DEBUG("QsoptexTheorySolver::CheckSat: no need to call LP solver");
    return sat_status;
  }

  // Now we call the solver
  int lp_status = -1;
  sat_status = SAT_NO_RESULT;
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::CheckSat: calling QSopt_ex (phase {})",
                    1 == config_.simplex_sat_phase() ? "one" : "two");

  *actual_precision = precision_;
  if (1 == config_.simplex_sat_phase()) {
    status = QSdelta_solver(prob, actual_precision->get_mpq_t(), static_cast<mpq_t *>(x), nullptr, nullptr,
                            PRIMAL_SIMPLEX, &lp_status,
                            config_.continuous_output() ? QsoptexCheckSatPartialSolution : nullptr,
                            this);
  } else {
    status = QSexact_delta_solver(prob, static_cast<mpq_t *>(x), nullptr, nullptr, PRIMAL_SIMPLEX,
                                  &lp_status, actual_precision->get_mpq_t(),
                                  config_.continuous_output() ? QsoptexCheckSatPartialSolution : nullptr,
                                  this);
  }

  if (status) {
    DLINEAR_RUNTIME_ERROR_FMT("QSopt_ex returned {}", status);
  } else {
    DLINEAR_DEBUG_FMT("QsoptexTheorySolver::CheckSat: QSopt_ex has returned with precision = {}", *actual_precision);
  }

  switch (lp_status) {
    case QS_LP_FEASIBLE:
    case QS_LP_DELTA_FEASIBLE:sat_status = SAT_DELTA_SATISFIABLE;
      break;
    case QS_LP_INFEASIBLE:sat_status = SAT_UNSATISFIABLE;
      break;
    case QS_LP_UNSOLVED:sat_status = SAT_UNSOLVED;
      break;
    default:DLINEAR_UNREACHABLE();
  }

  if (sat_status == SAT_UNSOLVED) {
    DLINEAR_DEBUG("QsoptexTheorySolver::CheckSat: QSopt_ex failed to return a result");
  }

  switch (sat_status) {
    case SAT_SATISFIABLE:
    case SAT_DELTA_SATISFIABLE:
      // Copy delta-feasible point from x into model_
      for (const pair<const int, Variable> &kv : var_map) {
        DLINEAR_ASSERT(model_[kv.second].lb() <= mpq_class(x[kv.first]) &&
            mpq_class(x[kv.first]) <= model_[kv.second].ub(), "x[kv.first] must be in bounds");
        model_[kv.second] = x[kv.first];
      }
      sat_status = SAT_DELTA_SATISFIABLE;
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

const Box &QsoptexTheorySolver::GetModel() const {
  DLINEAR_DEBUG_FMT("QsoptexTheorySolver::GetModel():\n{}", model_);
  return model_;
}

const LiteralSet &QsoptexTheorySolver::GetExplanation() const {
  return explanation_;
}

} // dlinear