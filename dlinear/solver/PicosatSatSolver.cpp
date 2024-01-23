//
// Created by c3054737 on 10/01/24.
//

#include "PicosatSatSolver.h"

#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

PicosatSatSolver::PicosatSatSolver(PredicateAbstractor &predicate_abstractor, const Config &config)
    : SatSolver{predicate_abstractor, config}, sat_(picosat_init()), has_picosat_pop_used_{false} {
  picosat_save_original_clauses(sat_);
  if (config.random_seed() != 0) {
    picosat_set_seed(sat_, config.random_seed());
    DLINEAR_DEBUG_FMT("PicosatSatSolver::Set Random Seed {}", config.random_seed());
  }
  picosat_set_global_default_phase(sat_, static_cast<int>(config.sat_default_phase()));
  DLINEAR_DEBUG_FMT("PicosatSatSolver::Set Default Phase {}", config.sat_default_phase());
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
  DLINEAR_DEBUG_FMT("PicosatSatSolver::MakeSatVar({} ↦ {})", var, sat_var);
}

void PicosatSatSolver::AddLearnedClause(const LiteralSet &literals) {
  for (const Literal &l : literals) AddLiteral({l.first, !(l.second)}, true);
  picosat_add(sat_, 0);
}

void PicosatSatSolver::AddLiteral(const Literal &l, bool learned) {
  const auto &[var, truth] = l;
  DLINEAR_ASSERT(var.get_type() == Variable::Type::BOOLEAN, "var must be Boolean");
  // f = b or f = ¬b.
  const int lit = truth ? var_to_sat_[var.get_id()] : -var_to_sat_[var.get_id()];
  picosat_add(sat_, lit);
  UpdateLookup(lit, learned);
  // If the literal is from the original formula, add it to the theory solver.
  if (!learned) theory_literals_.emplace_back(var, l.second);
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
  static IterationStats stat{DLINEAR_INFO_ENABLED, "PicosatSatSolver", "Total time spent in SAT checks",
                             "Total # of CheckSat"};
  DLINEAR_DEBUG_FMT("PicosatSatSolver::CheckSat(#vars = {}, #clauses = {})", picosat_variables(sat_),
                    picosat_added_original_clauses(sat_));
  TimerGuard check_sat_timer_guard(&stat.m_timer(), DLINEAR_INFO_ENABLED);
  stat.Increase();

  // Call SAT solver.
  const int ret{picosat_sat(sat_, -1)};
  check_sat_timer_guard.pause();

  if (ret == PICOSAT_SATISFIABLE) {
    return OnSatResult();
  } else if (ret == PICOSAT_UNSATISFIABLE) {
    DLINEAR_DEBUG("PicosatSatSolver::CheckSat() No solution.");
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
