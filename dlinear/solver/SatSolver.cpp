/**
 * @file SatSolver.cpp
 * @author dlinear (https://github.com/TendTo/dlinear)
 * @copyright 2024 dlinear
 * @licence Apache-2.0 license
 */
#include "SatSolver.h"

#include <cstdlib>
#include <unordered_map>
#include <utility>

#include "dlinear/util/exception.h"
#include "dlinear/util/logging.h"

namespace dlinear {

SatSolver::SatSolver(PredicateAbstractor &predicate_abstractor, const std::string &class_name)
    : config_{predicate_abstractor.config()},
      cur_clause_start_{0},
      cnfizer_{predicate_abstractor.config()},
      predicate_abstractor_{predicate_abstractor},
      stats_{config_.with_timings(), class_name, "Total time spent in CheckSat", "Total # of CheckSat"} {}

const IterationStats &SatSolver::cnfizer_stats() const { return cnfizer_.stats(); }

void SatSolver::AddFormula(const Formula &f) {
  DLINEAR_DEBUG_FMT("SatSolver::AddFormula({})", f);
  std::vector<Formula> clauses{cnfizer_.Convert(f)};

  // Collect CNF variables and store them in `cnf_variables_`.
  for (const auto &p : cnfizer_.vars()) cnf_variables_.insert(p.get_id());
  // Convert a first-order clauses into a Boolean formula by predicate abstraction
  // The original can be retrieved by `predicate_abstractor_[abstracted_formula]`.
  for (Formula &clause : clauses) clause = predicate_abstractor_.Convert(clause);

  AddClauses(clauses);
}

void SatSolver::Pop() { DLINEAR_RUNTIME_ERROR("Not implemented"); }
void SatSolver::Push() { DLINEAR_RUNTIME_ERROR("Not implemented"); }

void SatSolver::AddFormulas(const std::vector<Formula> &formulas) {
  for (const Formula &f : formulas) AddFormula(f);
}

void SatSolver::AddClauses(const std::vector<Formula> &formulas) {
  for (const Formula &f : formulas) AddClause(f);
}

void SatSolver::AddClause(const Formula &f) {
  DLINEAR_DEBUG_FMT("ContextImpl::AddClause({})", f);
  // Set up Variable ⇔ Literal (in SAT) map.
  for (const Variable &var : f.GetFreeVariables()) MakeSatVar(var);
  // Add clauses to SAT solver.
  AddClauseToSat(f);
}

void SatSolver::AddLiteral(const Formula &f) {
  DLINEAR_ASSERT_FMT(is_variable(f) || (is_negation(f) && is_variable(get_operand(f))),
                     "f must be a variable or negation of a variable. Found {}", f);
  if (is_variable(f)) {
    AddLiteral({get_variable(f), true}, false);
  } else {
    AddLiteral({get_variable(get_operand(f)), false}, false);
  }
}

void SatSolver::UpdateLookup(int lit, int learned) {
  if (!learned) {
    main_clauses_copy_.push_back(lit);
    main_clause_lookup_[lit].insert(cur_clause_start_);
  }
}

void SatSolver::GetMainActiveLiterals(std::set<int> &lits) const {
  std::set<size_t> examined_clauses_idx;
  for (auto it = lits.begin(); it != lits.end();) {
    int i = *it;
    int required = false;
    // Determine whether literal `i' is required
    auto c_it = main_clause_lookup_.find(i);
    if (c_it != main_clause_lookup_.end()) {
      for (size_t c : c_it->second) {
        // Make sure 'c' is a clause we haven't checked yet
        if (examined_clauses_idx.count(c) > 0) continue;
        int count = 0;
        size_t j;
        for (j = c; j < main_clauses_copy_.size() && main_clauses_copy_[j]; ++j) {
          int k = main_clauses_copy_[j];
          if (lits.find(k) != lits.end()) ++count;
        }
        DLINEAR_ASSERT(j < main_clauses_copy_.size(), "buffer overrun");
        DLINEAR_ASSERT(count > 0, "should contain at least 'i'");
        if (count == 1) {
          // `i' is the only active literal in clause `c'; hence, required.
          required = true;
          break;
        } else {
          // There are at least two active literals in clause 'c'. There is no point in checking it again
          examined_clauses_idx.insert(c);
        }
      }
    }
    // There is more than one literal in every main (non-learned) clause
    // containing literal `i'.  Hence, it is not required.
    if (!required) {
      it = lits.erase(it);
    } else {
      ++it;
    }
  }
}

Model SatSolver::OnSatResult() {
  Model model;

  for (int i : GetMainActiveLiterals()) {
    const auto it_var = sat_to_var_.find(abs(i));
    if (it_var == sat_to_var_.end()) {
      // There is no symbolic::Variable corresponding to this
      // picosat variable (int). This could be because of picosat_push/pop.
      continue;
    }
    const Variable &var{it_var->second};
    const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
    const auto it = var_to_formula_map.find(var);
    if (it != var_to_formula_map.end()) {  // The variable is a theory literal
      DLINEAR_TRACE_FMT("SatSolver::CheckSat: Add theory literal {}{} to Model", i > 0 ? "" : "¬", var);
      model.second.emplace_back(var, i > 0);
    } else if (cnf_variables_.count(var.get_id()) == 0) {  // The variable wasn't introduced by CNF transformations
      DLINEAR_TRACE_FMT("SatSolver::CheckSat: Add Boolean literal {}{} to Model ", i > 0 ? "" : "¬", var);
      model.first.emplace_back(var, i > 0);
    } else {  // The variable was introduced by CNF transformations
      DLINEAR_TRACE_FMT("SatSolver::CheckSat: Skip {}{} which is a temporary variable.", i > 0 ? "" : "¬", var);
    }
  }
  DLINEAR_DEBUG("SatSolver::CheckSat() Found a model.");
  //  DLINEAR_TRACE_FMT("SatSolver::CheckSat(): Model: {}", model);
  return model;
}

}  // namespace dlinear
