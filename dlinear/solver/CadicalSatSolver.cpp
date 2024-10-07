/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 */
#include "CadicalSatSolver.h"

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

CadicalSatSolver::CadicalSatSolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : SatSolver(predicate_abstractor, class_name), next_var_id_{1} {
  if (config_.random_seed() != 0) {
    [[maybe_unused]] const bool res = sat_.set("seed", static_cast<int>(config_.random_seed()));
    DLINEAR_ASSERT(res, "Failed to set random seed.");
    DLINEAR_DEBUG_FMT("CadicalSatSolver::Set Random Seed {}", config_.random_seed());
  }
  [[maybe_unused]] const bool res = sat_.set("phase", config_.sat_default_phase() != Config::SatDefaultPhase::False);
  DLINEAR_ASSERT(res, "Failed to set default phase.");
  DLINEAR_DEBUG_FMT("CadicalSatSolver::Set Default Phase {}", config_.sat_default_phase());
}

void CadicalSatSolver::MakeSatVar(const Variable &var) {
  auto it = var_to_sat_.find(var.get_id());
  // Found, no need to create the mapping
  if (it != var_to_sat_.end()) return;

  // It's not in the maps, let's make one and add it.
  const int sat_var = next_var_id_++;
  sat_.add_observed_var(sat_var);
  var_to_sat_.insert(var.get_id(), sat_var);
  sat_to_var_.insert(sat_var, var);
  DLINEAR_DEBUG_FMT("CadicalSatSolver::MakeSatVar({} ↦ {})", var, sat_var);
}

void CadicalSatSolver::AddLearnedClause(const LiteralSet &literals) {
  for (const Literal &lit : literals) AddLiteral(!lit, true);
  sat_.add(0);
}
void CadicalSatSolver::AddLearnedClause(const Literal &lit) {
  AddLiteral(!lit, true);
  sat_.add(0);
}

void CadicalSatSolver::AddLiteral(const Literal &l, bool learned) {
  const auto &[var, truth] = l;
  DLINEAR_ASSERT(var.get_type() == Variable::Type::BOOLEAN, "var must be Boolean");
  // f = b or f = ¬b.
  const int lit = truth ? var_to_sat_[var.get_id()] : -var_to_sat_[var.get_id()];
  sat_.add(lit);
  // If the literal is from the original formula, update the mapping lookup.
  if (!learned) UpdateLookup(lit);
}

std::set<int> CadicalSatSolver::GetMainActiveLiterals() {
  std::set<int> lits;
  for (int i = 1; i <= sat_.vars(); ++i) {
    const int lit = sat_.val(i);
    if (lit == 0) continue;
    lits.insert(lit);
  }
  SatSolver::GetMainActiveLiterals(lits);
  return lits;
}

std::optional<Model> CadicalSatSolver::CheckSat() {
  TimerGuard timer_guard(&stats_.m_timer(), stats_.enabled());
  stats_.Increase();

  DLINEAR_DEBUG_FMT("CadicalSatSolver::CheckSat(#vars = {}, #active = {})", sat_.vars(), sat_.active());

  // Call SAT solver.
  const int ret = sat_.solve();

  if (ret == CaDiCaL::Status::SATISFIABLE) {
    return OnSatResult();
  } else if (ret == CaDiCaL::Status::UNSATISFIABLE) {
    DLINEAR_DEBUG("CadicalSatSolver::CheckSat() No solution.");
    return {};
  } else {
    DLINEAR_ASSERT(ret == CaDiCaL::Status::UNKNOWN, "ret must be UNKNOWN");
    DLINEAR_RUNTIME_ERROR("CaDiCaL returned UNKNOWN.");
  }
}

void CadicalSatSolver::AddClauseToSat(const Formula &f) {
  cur_clause_start_ = main_clauses_copy_.size();
  if (is_disjunction(f)) {
    // f = l₁ ∨ ... ∨ lₙ
    for (const Formula &l : get_operands(f)) SatSolver::AddLiteral(l);
  } else {
    // f = b or f = ¬b.
    SatSolver::AddLiteral(f);
  }
  sat_.add(0);
  main_clauses_copy_.push_back(0);
}

void CadicalSatSolver::FixedTheoryLiterals(LiteralSet &fixed_literals) {
  for (int i = 1; i <= sat_.vars(); ++i) {
    const int lit = sat_.fixed(i);
    if (lit == 0) continue;
    const Variable &var = sat_to_var_[i];
    if (predicate_abstractor_.var_to_formula_map().contains(var)) fixed_literals.emplace(var, lit > 0);
  }
  DLINEAR_TRACE_FMT("CadicalSatSolver::FixedTheoryLiterals({})", fixed_literals);
}
void CadicalSatSolver::Assume(const Literal &l) {
  DLINEAR_TRACE_FMT("CadicalSatSolver::Assume({})", l);
  sat_.assume(l.truth ? var_to_sat_[l.var.get_id()] : -var_to_sat_[l.var.get_id()]);
}

void CadicalSatSolver::Push() {
  DLINEAR_DEBUG("CadicalSatSolver::Push()");
  // TODO(tend): push
  var_to_sat_.push();
  sat_to_var_.push();
  cnf_variables_.push();
  DLINEAR_RUNTIME_ERROR("cadical pop is not implemented.");
}
void CadicalSatSolver::Pop() {
  DLINEAR_DEBUG("CadicalSatSolver::Pop()");
  cnf_variables_.pop();
  var_to_sat_.pop();
  sat_to_var_.pop();
  // TODO(tend): pop
  DLINEAR_RUNTIME_ERROR("cadical pop is not implemented.");
}

}  // namespace dlinear