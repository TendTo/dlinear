//
// Created by c3054737 on 10/01/24.
//

#include "PicosatSatSolver.h"

#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

namespace {
class PicosatSatSolverStat : public Stats {
 public:
  explicit PicosatSatSolverStat(const bool enabled) : Stats{enabled} {};
  PicosatSatSolverStat(const PicosatSatSolverStat &) = default;
  PicosatSatSolverStat(PicosatSatSolverStat &&) = default;
  PicosatSatSolverStat &operator=(const PicosatSatSolverStat &) = delete;
  PicosatSatSolverStat &operator=(PicosatSatSolverStat &&) = delete;
  ~PicosatSatSolverStat() override {
    if (enabled()) std::cout << ToString() << std::endl;
  }
  [[nodiscard]] std::string ToString() const override {
    return fmt::format(DLINEAR_STATS_FMT, "Total # of CheckSat", "SAT level", num_check_sat_,
                       "Total time spent in SAT checks", "SAT level", timer_check_sat_.seconds());
  }
  int num_check_sat_{0};
  Timer timer_check_sat_;
};
}  // namespace

PicosatSatSolver::PicosatSatSolver(const Config &config)
    : SatSolver{config}, sat_(picosat_init()), has_picosat_pop_used_{false} {
  picosat_save_original_clauses(sat_);
  if (config.random_seed() != 0) {
    picosat_set_seed(sat_, config.random_seed());
    DLINEAR_DEBUG_FMT("SoplexSatSolver::Set Random Seed {}", config.random_seed());
  }
  picosat_set_global_default_phase(sat_, static_cast<int>(config.sat_default_phase()));
  DLINEAR_DEBUG_FMT("SoplexSatSolver::Set Default Phase {}", config.sat_default_phase());
}
PicosatSatSolver::~PicosatSatSolver() { picosat_reset(sat_); }

void PicosatSatSolver::MakeSatVar(const Variable &var) {
  auto it = var_to_sat_.find(var.get_id());
  // Found, no need to create the mapping
  if (it != var_to_sat_.end()) return;

  // It's not in the maps, let's make one and add it.
  const int sat_var{picosat_inc_max_var(sat_)};
  var_to_sat_.insert(var.get_id(), sat_var);
  sat_to_var_.insert(sat_var, var);
  DLINEAR_DEBUG_FMT("SoplexSatSolver::MakeSatVar({} ↦ {})", var, sat_var);
}

void PicosatSatSolver::AddLearnedClause(const LiteralSet &literals) {
  for (const Literal &l : literals) AddLiteral({l.first, !(l.second)}, true);
  picosat_add(sat_, 0);
}

void PicosatSatSolver::AddLiteral(const Literal &l, bool learned) {
  const Variable &var{l.first};
  DLINEAR_ASSERT(var.get_type() == Variable::Type::BOOLEAN, "var must be Boolean");
  if (l.second) {
    // f = b
    // Add l = b
    int lit{var_to_sat_[var.get_id()]};
    picosat_add(sat_, lit);
    UpdateLookup(lit, learned);
    // TODO: if (!learned) AddLinearLiteral(var, true);
  } else {
    // f = ¬b
    // Add l = ¬b
    int lit{-var_to_sat_[var.get_id()]};
    picosat_add(sat_, lit);
    UpdateLookup(lit, learned);
    // TODO: if (!learned) AddLinearLiteral(var, false);
  }
}

std::set<int> PicosatSatSolver::GetMainActiveLiterals() const {
  std::set<int> lits;
  for (int i = 1; i <= picosat_variables(sat_); ++i) {
    const int model_i = has_picosat_pop_used_ ? picosat_deref(sat_, i) : picosat_deref_partial(sat_, i);
    if (model_i == 0) continue;
    lits.insert(model_i * i);
  }
  // Use the superclass method to filter out literals that are not
  // required by main clauses.
  SatSolver::GetMainActiveLiterals(lits);
  return lits;
}

std::optional<Model> PicosatSatSolver::CheckSat() {
  static PicosatSatSolverStat stat{DLINEAR_INFO_ENABLED};
  DLINEAR_DEBUG_FMT("SoplexSatSolver::CheckSat(#vars = {}, #clauses = {})", picosat_variables(sat_),
                    picosat_added_original_clauses(sat_));
  stat.num_check_sat_++;
  // Call SAT solver.
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, DLINEAR_INFO_ENABLED);
  const int ret{picosat_sat(sat_, -1)};
  check_sat_timer_guard.pause();

  if (ret == PICOSAT_SATISFIABLE) {
    return OnSatResult();
  } else if (ret == PICOSAT_UNSATISFIABLE) {
    DLINEAR_DEBUG("SoplexSatSolver::CheckSat() No solution.");
    return {};
  } else {
    DLINEAR_ASSERT(ret == PICOSAT_UNKNOWN, "ret must be PICOSAT_UNKNOWN");
    DLINEAR_RUNTIME_ERROR("PICOSAT returns PICOSAT_UNKNOWN.");
  }
}

void PicosatSatSolver::AddClauseToSat(const Formula &f) {
  cur_clause_start_ = main_clauses_copy_.size();
  if (is_disjunction(f)) {
    // f = l₁ ∨ ... ∨ lₙ
    for (const Formula &l : get_operands(f)) {
      SatSolver::AddLiteral(l);
    }
  } else {
    // f = b or f = ¬b.
    SatSolver::AddLiteral(f);
  }
  picosat_add(sat_, 0);
  main_clauses_copy_.push_back(0);
}

}  // namespace dlinear