/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
// IWYU pragma: no_include "picosat/picosat.h" // Already included in the header
#include "PicosatSatSolver.h"

#include <unordered_map>
#include <vector>

#include "dlinear/util/Config.h"
#include "dlinear/util/ScopedUnorderedMap.hpp"
#include "dlinear/util/Stats.h"
#include "dlinear/util/Timer.h"
#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

PicosatSatSolver::PicosatSatSolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : SatSolver{predicate_abstractor, class_name}, sat_(picosat_init()), has_picosat_pop_used_{false} {
  picosat_save_original_clauses(sat_);
  if (config_.random_seed() != 0) {
    picosat_set_seed(sat_, config_.random_seed());
    DLINEAR_DEBUG_FMT("PicosatSatSolver::Set Random Seed {}", config_.random_seed());
  }
  picosat_set_global_default_phase(sat_, static_cast<int>(config_.sat_default_phase()));
  DLINEAR_DEBUG_FMT("PicosatSatSolver::Set Default Phase {}", config_.sat_default_phase());
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
  for (const Literal &lit : literals) AddLiteral(!lit, true);
  picosat_add(sat_, 0);
}
void PicosatSatSolver::AddLearnedClause(const Literal &lit) {
  AddLiteral(!lit, true);
  picosat_add(sat_, 0);
}

void PicosatSatSolver::AddLiteral(const Literal &l, bool learned) {
  const auto &[var, truth] = l;
  DLINEAR_ASSERT(var.get_type() == Variable::Type::BOOLEAN, "var must be Boolean");
  // f = b or f = ¬b.
  const int lit = truth ? var_to_sat_[var.get_id()] : -var_to_sat_[var.get_id()];
  picosat_add(sat_, lit);
  // If the literal is from the original formula, update the mapping lookup.
  if (!learned) UpdateLookup(lit);
}

std::set<int> PicosatSatSolver::GetMainActiveLiterals() {
  std::set<int> lits;
  for (int i = 1; i <= picosat_variables(sat_); ++i) {
    const int lit = i * (has_picosat_pop_used_ ? picosat_deref(sat_, i) : picosat_deref_partial(sat_, i));
    if (lit == 0) continue;
    lits.insert(lit);
  }
  // Use the superclass method to filter out literals that are not required by main clauses.
  SatSolver::GetMainActiveLiterals(lits);
  return lits;
}

std::optional<Model> PicosatSatSolver::CheckSat() {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_DEBUG_FMT("PicosatSatSolver::CheckSat(#vars = {}, #clauses = {})", picosat_variables(sat_),
                    picosat_added_original_clauses(sat_));

  // Call SAT solver.
  const int ret{picosat_sat(sat_, -1)};

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
    for (const Formula &l : get_operands(f)) SatSolver::AddLiteral(l);
  } else {
    // f = b or f = ¬b.
    SatSolver::AddLiteral(f);
  }
  picosat_add(sat_, 0);
  main_clauses_copy_.push_back(0);
}

void PicosatSatSolver::FixedTheoryLiterals(LiteralSet &fixed_literals) {
  std::vector<int> clause;
  clause.reserve(main_clauses_copy_.size());
  for (const int sat_lit : main_clauses_copy_) {
    if (sat_lit == 0) {
      if (clause.size() == 1) {
        DLINEAR_ASSERT(clause[0] != 0, "Clause must be either true or false");
        const Variable &var = sat_to_var_[abs(clause[0])];
        if (predicate_abstractor_.var_to_formula_map().contains(var)) fixed_literals.emplace(var, clause[0] > 0);
      }
      clause.clear();
      continue;
    }
    clause.push_back(sat_lit);
  }
  DLINEAR_TRACE_FMT("PicosatSatSolver::FixedTheoryLiterals() fixed_literals = {}", fixed_literals);
}

void PicosatSatSolver::Assume(const Literal &lit) {
  DLINEAR_TRACE_FMT("PicosatSatSolver::Assume({})", lit);
  picosat_assume(sat_, lit.truth ? var_to_sat_[lit.var.get_id()] : -var_to_sat_[lit.var.get_id()]);
}

void PicosatSatSolver::Push() {
  DLINEAR_DEBUG("PicosatSatSolver::Push()");
  picosat_push(sat_);
  var_to_sat_.push();
  sat_to_var_.push();
  cnf_variables_.push();
  DLINEAR_RUNTIME_ERROR("picosat_push is bugged.");
}
void PicosatSatSolver::Pop() {
  DLINEAR_DEBUG("PicosatSatSolver::Pop()");
  cnf_variables_.pop();
  var_to_sat_.pop();
  sat_to_var_.pop();
  picosat_pop(sat_);
  has_picosat_pop_used_ = true;
  DLINEAR_RUNTIME_ERROR("picosat_pop is bugged.");
}

}  // namespace dlinear
