/**
 * @file QsoptexSatSolver.cpp
 * @author dlinear
 * @date 17 Aug 2023
 * @copyright 2023 dlinear
 * @brief Brief description
 *
 * Long Description
 */

#include "QsoptexSatSolver.h"

using std::cout;
using std::set;
using std::vector;
using std::pair;
using std::make_pair;
using std::abs;
using tl::optional;

namespace dlinear {

QsoptexSatSolver::QsoptexSatSolver(const Config &config) : sat_{picosat_init()},
                                                           cur_clause_start_{0}, config_(config) {
  // Enable partial checks via picosat_deref_partial. See the call-site in
  // QsoptexSatSolver::CheckSat().
  picosat_save_original_clauses(sat_);
  if (config.random_seed() != 0) {
    picosat_set_seed(sat_, config.random_seed());
    DLINEAR_DEBUG_FMT("QsoptexSatSolver::Set Random Seed {}", config.random_seed());
  }
  picosat_set_global_default_phase(
      sat_, static_cast<int>(config.sat_default_phase()));
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::Set Default Phase {}", config.sat_default_phase());
  qsx_prob_ = mpq_QScreate_prob(NULL, QS_MIN);
  DLINEAR_ASSERT(qsx_prob_, "Failed to create QSopt_ex problem");
  if (config_.verbose_simplex() > 3) {
    DLINEAR_RUNTIME_ERROR("With --lp-solver qsoptex, maximum value for --verbose-simplex is 3");
  }
  mpq_QSset_param(qsx_prob_, QS_PARAM_SIMPLEX_DISPLAY, config_.verbose_simplex());
}

QsoptexSatSolver::QsoptexSatSolver(const Config &config, const vector <Formula> &clauses)
    : QsoptexSatSolver{config} {
  AddClauses(clauses);
}

QsoptexSatSolver::~QsoptexSatSolver() {
  picosat_reset(sat_);
  mpq_QSfree_prob(qsx_prob_);
}

void QsoptexSatSolver::AddFormula(const Formula &f) {
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::AddFormula({})", f);
  vector<Formula> clauses{cnfizer_.Convert(f)};
  // Collect CNF variables.
  for (const auto &p : cnfizer_.vars()) {
    cnf_variables_.insert(p.get_id());
  }
  for (Formula &clause : clauses) {
    clause = predicate_abstractor_.Convert(clause);
  }
  AddClauses(clauses);
}

void QsoptexSatSolver::AddFormulas(const vector <Formula> &formulas) {
  for (const Formula &f : formulas) {
    AddFormula(f);
  }
}

void QsoptexSatSolver::AddLearnedClause(const LiteralSet &literals) {
  for (const Literal &l : literals) {
    AddLiteral(make_pair(l.first, !(l.second)), true);
  }
  picosat_add(sat_, 0);
}

void QsoptexSatSolver::AddClauses(const vector <Formula> &formulas) {
  for (const Formula &f : formulas) {
    AddClause(f);
  }
}

void QsoptexSatSolver::AddClause(const Formula &f) {
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::AddClause({})", f);
  // Set up Variable ⇔ Literal (in SAT) map.
  for (const Variable &var : f.GetFreeVariables()) {
    MakeSatVar(var);
  }
  // Add clauses to SAT solver.
  DoAddClause(f);
}

namespace {
class SatSolverStat : public Stats {
 public:
  explicit SatSolverStat(const bool enabled) : Stats{enabled} {};
  SatSolverStat(const SatSolverStat &) = default;
  SatSolverStat(SatSolverStat &&) = default;
  SatSolverStat &operator=(const SatSolverStat &) = delete;
  SatSolverStat &operator=(SatSolverStat &&) = delete;
  ~SatSolverStat() override {
    if (enabled()) {
      using fmt::print;
      print(cout, "{:<45} @ {:<20} = {:>15}\n", "Total # of CheckSat",
            "SAT level", num_check_sat_);
      print(cout, "{:<45} @ {:<20} = {:>15f} sec\n",
            "Total time spent in SAT checks", "SAT level",
            timer_check_sat_.seconds());
    }
  }

  int num_check_sat_{0};
  Timer timer_check_sat_;
};
}  // namespace

// Collect active literals, removing those that are only required by learned
// clauses.
set<int> QsoptexSatSolver::GetMainActiveLiterals() const {
  set<int> lits;
  for (int i = 1; i <= picosat_variables(sat_); ++i) {
    const int model_i{has_picosat_pop_used_ ? picosat_deref(sat_, i)
                                            : picosat_deref_partial(sat_, i)};
    if (model_i == 0) {
      continue;
    }
    lits.insert(model_i * i);
  }
  for (auto it = lits.begin(); it != lits.end();) {
    int i = *it;
    int required = false;
    // Determine whether literal `i' is required
    auto c_it = main_clause_lookup_.find(i);
    if (c_it != main_clause_lookup_.end()) {
      for (int c : c_it->second) {
        int count = 0;
        size_t j;
        for (j = c; j < main_clauses_copy_.size() &&
            main_clauses_copy_[j]; ++j) {
          int k{main_clauses_copy_[j]};
          if (lits.find(k) != lits.end()) {
            ++count;
          }
        }
        DLINEAR_ASSERT(j < main_clauses_copy_.size(), "Buffer overrun");
        DLINEAR_ASSERT(count > 0, "Should contain at least 'i'");
        if (count == 1) {
          // `i' is the only active literal in clause `c'; hence, required.
          required = true;
          break;
        }
      }
    }
    if (!required) {
      // There is more than one literal in every main (non-learned) clause
      // containing literal `i'.  Hence, it is not required.
      it = lits.erase(it);
    } else {
      ++it;
    }
  }
  return lits;
}

optional <QsoptexSatSolver::Model>
QsoptexSatSolver::CheckSat(const Box &box, const optional <Expression> obj_expr) {
  static SatSolverStat stat{DLINEAR_INFO_ENABLED};
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::CheckSat(#vars = {}, #clauses = {})",
                    picosat_variables(sat_),
                    picosat_added_original_clauses(sat_));

  if (obj_expr.has_value()) {
    DLINEAR_TRACE_FMT("QsoptexSatSolver::CheckSat: Objective = {}", *obj_expr);
    SetLinearObjective(*obj_expr);
  } else {
    ClearLinearObjective();
  }

  stat.num_check_sat_++;
  // Call SAT solver.
  TimerGuard check_sat_timer_guard(&stat.timer_check_sat_, DLINEAR_INFO_ENABLED);
  const int ret{picosat_sat(sat_, -1)};
  check_sat_timer_guard.pause();

  Model model;
  if (ret == PICOSAT_SATISFIABLE) {
    // SAT Case.
    set<int> lits{GetMainActiveLiterals()};
    ResetLinearProblem(box);
    const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
    for (int i : lits) {
      const auto it_var = to_sym_var_.find(abs(i));
      if (it_var == to_sym_var_.end()) {
        // There is no symbolic::Variable corresponding to this
        // picosat variable (int). This could be because of
        // picosat_push/pop.
        continue;
      }
      const Variable &var{it_var->second};
      const auto it = var_to_formula_map.find(var);
      if (it != var_to_formula_map.end()) {
        DLINEAR_TRACE_FMT("QsoptexSatSolver::CheckSat: Add theory literal {}{} to Model", i > 0 ? "" : "¬", var);
        auto &theory_model = model.second;
        theory_model.emplace_back(var, i > 0);
        EnableLinearLiteral(var, i > 0);
      } else if (cnf_variables_.count(var.get_id()) == 0) {
        DLINEAR_TRACE_FMT("QsoptexSatSolver::CheckSat: Add Boolean literal {}{} to Model ", i > 0 ? "" : "¬", var);
        auto &boolean_model = model.first;
        boolean_model.emplace_back(var, i > 0);
      } else {
        DLINEAR_TRACE_FMT("QsoptexSatSolver::CheckSat: Skip {}{} which is a temporary variable.",
                          i > 0 ? "" : "¬",
                          var);
      }
    }
    DLINEAR_DEBUG_FMT("QsoptexSatSolver::CheckSat() Found a model.");
    return model;
  } else if (ret == PICOSAT_UNSATISFIABLE) {
    DLINEAR_DEBUG_FMT("QsoptexSatSolver::CheckSat() No solution.");
    // UNSAT Case.
    return {};
  } else {
    DLINEAR_ASSERT(ret == PICOSAT_UNKNOWN, "Unexpected return value");
    DLINEAR_RUNTIME_ERROR("PICOSAT returns PICOSAT_UNKNOWN.");
  }
}

void QsoptexSatSolver::Pop() {
  // FIXME: disabled for QSopt_ex changes
  DLINEAR_RUNTIME_ERROR("QsoptexSatSolver::Pop() currently unsupported");
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::Pop()");
  cnf_variables_.pop();
  to_sym_var_.pop();
  to_sat_var_.pop();
  picosat_pop(sat_);
  has_picosat_pop_used_ = true;
}

void QsoptexSatSolver::Push() {
  // FIXME: disabled for QSopt_ex changes
  DLINEAR_RUNTIME_ERROR("QsoptexSatSolver::Push() currently unsupported");
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::Push()");
  picosat_push(sat_);
  to_sat_var_.push();
  to_sym_var_.push();
  cnf_variables_.push();
}

void QsoptexSatSolver::SetQSXVarCoef(int qsx_row, const Variable &var,
                                     const mpq_class &value) {
  const auto it = to_qsx_col_.find(var.get_id());
  if (it == to_qsx_col_.end()) {
    DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}");
  }
  if (value <= mpq_ninfty() || value >= mpq_infty()) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);
  }
  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  mpq_QSchange_coef(qsx_prob_, qsx_row, it->second, c_value);
  mpq_clear(c_value);
}

void QsoptexSatSolver::SetQSXVarObjCoef(const Variable &var,
                                        const mpq_class &value) {
  const auto it = to_qsx_col_.find(var.get_id());
  if (it == to_qsx_col_.end()) {
    DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);
  }
  if (value <= mpq_ninfty() || value >= mpq_infty()) {
    DLINEAR_RUNTIME_ERROR_FMT("LP coefficient too large: {}", value);
  }
  mpq_t c_value;
  mpq_init(c_value);
  mpq_set(c_value, value.get_mpq_t());
  mpq_QSchange_objcoef(qsx_prob_, it->second, c_value);
  mpq_clear(c_value);
}

void QsoptexSatSolver::SetQSXVarBound(const Variable &var, const char type,
                                      const mpq_class &value) {
  if (type == 'B') {
    // Both
    SetQSXVarBound(var, 'L', value);
    SetQSXVarBound(var, 'U', value);
    return;
  }
  DLINEAR_ASSERT(type == 'L' || type == 'U', "Type must be 'L' or 'U'");
  const auto it = to_qsx_col_.find(var.get_id());
  if (it == to_qsx_col_.end()) {
    DLINEAR_RUNTIME_ERROR_FMT("Variable undefined: {}", var);
  }
  if (value <= mpq_ninfty() || value >= mpq_infty()) {
    DLINEAR_RUNTIME_ERROR_FMT("Simple bound too large: {}", value);
  }
  mpq_t c_value;
  mpq_init(c_value);
  mpq_QSget_bound(qsx_prob_, it->second, type, &c_value);
  mpq_class existing{c_value};
  if ((type == 'L' && existing < value) || (type == 'U' && value < existing)) {
    mpq_set(c_value, value.get_mpq_t());
    mpq_QSchange_bound(qsx_prob_, it->second, type, c_value);
  }
  mpq_clear(c_value);
}

void QsoptexSatSolver::ResetLinearProblem(const Box &box) {
  DLINEAR_TRACE_FMT("QsoptexSatSolver::ResetLinearProblem(): Box =\n{}", box);
  // Clear constraint bounds
  const int qsx_rows{mpq_QSget_rowcount(qsx_prob_)};
  DLINEAR_ASSERT(static_cast<size_t>(qsx_rows) == from_qsx_row_.size(), "Row count mismatch");
  for (int i = 0; i < qsx_rows; i++) {
    mpq_QSchange_sense(qsx_prob_, i, 'G');
    mpq_QSchange_rhscoef(qsx_prob_, i, mpq_NINFTY);
  }
  // Clear variable bounds
  const int qsx_cols{mpq_QSget_colcount(qsx_prob_)};
  DLINEAR_ASSERT(static_cast<size_t>(qsx_cols) == from_qsx_col_.size(), "Column count mismatch");
  for (const pair<int, Variable> kv : from_qsx_col_) {
    if (box.has_variable(kv.second)) {
      DLINEAR_ASSERT(mpq_ninfty() <= box[kv.second].lb(), "Lower bound too low");
      DLINEAR_ASSERT(box[kv.second].lb() <= box[kv.second].ub(), "Lower bound must be smaller than upper bound");
      DLINEAR_ASSERT(box[kv.second].ub() <= mpq_infty(), "Upper bound too high");
      mpq_QSchange_bound(qsx_prob_, kv.first, 'L', box[kv.second].lb().get_mpq_t());
      mpq_QSchange_bound(qsx_prob_, kv.first, 'U', box[kv.second].ub().get_mpq_t());
    } else {
      mpq_QSchange_bound(qsx_prob_, kv.first, 'L', mpq_NINFTY);
      mpq_QSchange_bound(qsx_prob_, kv.first, 'U', mpq_INFTY);
    }
  }
}

static bool is_simple_bound(const Formula &formula) {
  if (!is_relational(formula)) {
    return false;
  }
  const Expression &lhs{get_lhs_expression(formula)};
  const Expression &rhs{get_rhs_expression(formula)};
  return ((is_constant(lhs) && is_variable(rhs)) ||
      (is_variable(lhs) && is_constant(rhs)));
}

// Because the input precision > 0, and we have reduced this by a small amount,
// we can replace any strict inequalities with the equivalent non-strict
// inequalities, and ignore not-equal constraints altogether.

static bool is_equal_or_whatever(const Formula &formula, bool truth) {
  if (truth) {
    return is_equal_to(formula);
  } else {
    return is_not_equal_to(formula);
  }
}

static bool is_not_equal_or_whatever(const Formula &formula, bool truth) {
  return is_equal_or_whatever(formula, !truth);
}

static bool is_greater_or_whatever(const Formula &formula, bool truth) {
  if (truth) {
    return is_greater_than(formula) || is_greater_than_or_equal_to(formula);
  } else {
    return is_less_than(formula) || is_less_than_or_equal_to(formula);
  }
}

static bool is_less_or_whatever(const Formula &formula, bool truth) {
  return is_greater_or_whatever(formula, !truth);
}

void QsoptexSatSolver::EnableLinearLiteral(const Variable &var, bool truth) {
  const auto it_row = to_qsx_row_.find(make_pair(var.get_id(), truth));
  if (it_row != to_qsx_row_.end()) {
    // A non-trivial linear literal from the input problem
    const int qsx_row = it_row->second;
    mpq_QSchange_sense(qsx_prob_, qsx_row, qsx_sense_[qsx_row]);
    mpq_QSchange_rhscoef(qsx_prob_, qsx_row, qsx_rhs_[qsx_row].get_mpq_t());
    DLINEAR_TRACE_FMT("QsoptexSatSolver::EnableLinearLiteral({})", qsx_row);
    return;
  }
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(var);
  if (it != var_to_formula_map.end() && is_simple_bound(it->second)) {
    // A simple bound - set it directly
    const Formula &formula{it->second};
    const Expression &lhs{get_lhs_expression(formula)};
    const Expression &rhs{get_rhs_expression(formula)};
    DLINEAR_TRACE_FMT("QsoptexSatSolver::EnableLinearLiteral({}{})", truth ? "" : "¬", formula);
    if (is_equal_or_whatever(formula, truth)) {
      if (is_variable(lhs) && is_constant(rhs)) {
        SetQSXVarBound(get_variable(lhs), 'B', get_constant_value(rhs));
      } else if (is_constant(lhs) && is_variable(rhs)) {
        SetQSXVarBound(get_variable(rhs), 'B', get_constant_value(lhs));
      } else {
        DLINEAR_UNREACHABLE();
      }
    } else if (is_greater_or_whatever(formula, truth)) {
      if (is_variable(lhs) && is_constant(rhs)) {
        SetQSXVarBound(get_variable(lhs), 'L', get_constant_value(rhs));
      } else if (is_constant(lhs) && is_variable(rhs)) {
        SetQSXVarBound(get_variable(rhs), 'U', get_constant_value(lhs));
      } else {
        DLINEAR_UNREACHABLE();
      }
    } else if (is_less_or_whatever(formula, truth)) {
      if (is_variable(lhs) && is_constant(rhs)) {
        SetQSXVarBound(get_variable(lhs), 'U', get_constant_value(rhs));
      } else if (is_constant(lhs) && is_variable(rhs)) {
        SetQSXVarBound(get_variable(rhs), 'L', get_constant_value(lhs));
      } else {
        DLINEAR_UNREACHABLE();
      }
    } else if (is_not_equal_or_whatever(formula, truth)) {
      // Nothing to do, because this constraint is always delta-sat for
      // delta > 0.
    } else {
      DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
    }
    return;
  }
  // Either a learned literal, or a not-equal literal from the input
  // problem.
  DLINEAR_TRACE_FMT("QsoptexSatSolver::EnableLinearLiteral: ignoring ({}, {})",
                    var, truth);
}

void QsoptexSatSolver::AddLinearLiteral(const Variable &formulaVar, bool truth) {
  const auto &var_to_formula_map = predicate_abstractor_.var_to_formula_map();
  const auto it = var_to_formula_map.find(formulaVar);
  if (it == var_to_formula_map.end()) {
    // Boolean variable - no need to involve theory solver
    return;
  }
  const auto it2 = to_qsx_row_.find(make_pair(formulaVar.get_id(), truth));
  if (it2 != to_qsx_row_.end()) {
    // Found.
    return;
  }
  // Theory formula
  const Formula &formula = it->second;
  // Create the LP solver variables
  for (const Variable &var : formula.GetFreeVariables()) {
    AddLinearVariable(var);
  }
  if (is_equal_or_whatever(formula, truth)) {
    if (is_simple_bound(formula)) {
      return;  // Just create simple bound in LP
    }
    qsx_sense_.push_back('E');
  } else if (is_greater_or_whatever(formula, truth)) {
    if (is_simple_bound(formula)) {
      return;
    }
    qsx_sense_.push_back('G');
  } else if (is_less_or_whatever(formula, truth)) {
    if (is_simple_bound(formula)) {
      return;
    }
    qsx_sense_.push_back('L');
  } else if (is_not_equal_or_whatever(formula, truth)) {
    // Nothing to do, because this constraint is always delta-sat for
    // delta > 0.
    return;
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Formula {} not supported", formula);
  }
  Expression expr;
  expr = (get_lhs_expression(formula) - get_rhs_expression(formula)).Expand();
  const int qsx_row{mpq_QSget_rowcount(qsx_prob_)};
  mpq_QSnew_row(qsx_prob_, mpq_NINFTY, 'G', NULL);  // Inactive
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == qsx_sense_.size() - 1, "Sense count mismatch");
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == qsx_rhs_.size(), "RHS count mismatch");
  qsx_rhs_.emplace_back(0);
  if (is_constant(expr)) {
    qsx_rhs_.back() = -get_constant_value(expr);
  } else if (is_variable(expr)) {
    SetQSXVarCoef(qsx_row, get_variable(expr), 1);
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1 || !is_variable(map.begin()->first) || !is_constant(map.begin()->second)
        || get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
    }
    SetQSXVarCoef(qsx_row,
                  get_variable(map.begin()->first),
                  get_constant_in_multiplication(expr));
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    for (const pair<const Expression, mpq_class> &pair : map) {
      if (!is_variable(pair.first)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
      }
      SetQSXVarCoef(qsx_row, get_variable(pair.first), pair.second);
    }
    qsx_rhs_.back() = -get_constant_in_addition(expr);
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported", expr);
  }
  if (qsx_rhs_.back() <= mpq_ninfty() || qsx_rhs_.back() >= mpq_infty()) {
    DLINEAR_RUNTIME_ERROR_FMT("LP RHS value too large: {}", qsx_rhs_.back());
  }
  // Update indexes
  to_qsx_row_.emplace(make_pair(make_pair(formulaVar.get_id(), truth), qsx_row));
  DLINEAR_ASSERT(static_cast<size_t>(qsx_row) == from_qsx_row_.size(), "Row count mismatch");
  from_qsx_row_.emplace_back(make_pair(formulaVar, truth));
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::AddLinearLiteral({}{} ↦ {})",
                    truth ? "" : "¬", it->second, qsx_row);
}

void QsoptexSatSolver::UpdateLookup(int lit, int learned) {
  if (learned) {
    learned_clause_lits_.insert(lit);
  } else {
    main_clauses_copy_.push_back(lit);
    main_clause_lookup_[lit].insert(cur_clause_start_);
  }
}

void QsoptexSatSolver::AddLiteral(const Literal &l, bool learned) {
  if (l.second) {
    // f = b
    const Variable &var{l.first};
    DLINEAR_ASSERT(var.get_type() == Variable::Type::BOOLEAN, "Variable must be Boolean");
    // Add l = b
    int lit{to_sat_var_[var.get_id()]};
    picosat_add(sat_, lit);
    UpdateLookup(lit, learned);
    if (!learned) {
      AddLinearLiteral(var, true);
    }
  } else {
    // f = ¬b
    const Variable &var{l.first};
    DLINEAR_ASSERT(var.get_type() == Variable::Type::BOOLEAN, "Variable must be Boolean");
    // Add l = ¬b
    int lit{-to_sat_var_[var.get_id()]};
    picosat_add(sat_, lit);
    UpdateLookup(lit, learned);
    if (!learned) {
      AddLinearLiteral(var, false);
    }
  }
}

void QsoptexSatSolver::AddLiteral(const Formula &f) {
  DLINEAR_ASSERT(is_variable(f) || (is_negation(f) && is_variable(get_operand(f))), "Formula must be a literal");
  if (is_variable(f)) {
    AddLiteral(make_pair(get_variable(f), true), false);
  } else {
    AddLiteral(make_pair(get_variable(get_operand(f)), false), false);
  }
}

void QsoptexSatSolver::DoAddClause(const Formula &f) {
  cur_clause_start_ = main_clauses_copy_.size();
  if (is_disjunction(f)) {
    // f = l₁ ∨ ... ∨ lₙ
    for (const Formula &l : get_operands(f)) {
      AddLiteral(l);
    }
  } else {
    // f = b or f = ¬b.
    AddLiteral(f);
  }
  picosat_add(sat_, 0);
  main_clauses_copy_.push_back(0);
}

void QsoptexSatSolver::MakeSatVar(const Variable &var) {
  auto it = to_sat_var_.find(var.get_id());
  if (it != to_sat_var_.end()) {
    // Found.
    return;
  }
  // It's not in the maps, let's make one and add it.
  const int sat_var{picosat_inc_max_var(sat_)};
  to_sat_var_.insert(var.get_id(), sat_var);
  to_sym_var_.insert(sat_var, var);
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::MakeSatVar({} ↦ {})", var, sat_var);
}

void QsoptexSatSolver::AddLinearVariable(const Variable &var) {
  auto it = to_qsx_col_.find(var.get_id());
  if (it != to_qsx_col_.end()) {
    // Found.
    return;
  }
  const int qsx_col{mpq_QSget_colcount(qsx_prob_)};
  int status = mpq_QSnew_col(qsx_prob_, mpq_zeroLpNum, mpq_NINFTY, mpq_INFTY,
                             var.get_name().c_str());
  DLINEAR_ASSERT(!status, "Invalid status");
  to_qsx_col_.emplace(make_pair(var.get_id(), qsx_col));
  from_qsx_col_[qsx_col] = var;
  DLINEAR_DEBUG_FMT("QsoptexSatSolver::AddLinearVariable({} ↦ {})", var, qsx_col);
}

void QsoptexSatSolver::ClearLinearObjective() {
  const int qsx_colcount{mpq_QSget_colcount(qsx_prob_)};
  mpq_t c_value;
  mpq_init(c_value);  // Initialized to zero
  for (int i = 0; i < qsx_colcount; ++i) {
    mpq_QSchange_objcoef(qsx_prob_, i, c_value);
  }
  mpq_clear(c_value);
}

void QsoptexSatSolver::SetLinearObjective(const Expression &expr) {
  ClearLinearObjective();
  if (is_constant(expr)) {
    if (0 != get_constant_value(expr)) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
  } else if (is_variable(expr)) {
    SetQSXVarObjCoef(get_variable(expr), 1);
  } else if (is_multiplication(expr)) {
    std::map<Expression, Expression> map = get_base_to_exponent_map_in_multiplication(expr);
    if (map.size() != 1
        || !is_variable(map.begin()->first)
        || !is_constant(map.begin()->second)
        || get_constant_value(map.begin()->second) != 1) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
    SetQSXVarObjCoef(get_variable(map.begin()->first),
                     get_constant_in_multiplication(expr));
  } else if (is_addition(expr)) {
    const std::map<Expression, mpq_class> &map = get_expr_to_coeff_map_in_addition(expr);
    if (0 != get_constant_in_addition(expr)) {
      DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
    }
    for (const pair<const Expression, mpq_class> &pair : map) {
      if (!is_variable(pair.first)) {
        DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
      }
      SetQSXVarObjCoef(get_variable(pair.first), pair.second);
    }
  } else {
    DLINEAR_RUNTIME_ERROR_FMT("Expression {} not supported in objective", expr);
  }
}

const std::map<int, Variable> &QsoptexSatSolver::GetLinearVarMap() const {
  DLINEAR_TRACE_FMT("QsoptexSatSolver::GetLinearVarMap(): from_qsx_col_ =");
  if (DLINEAR_TRACE_ENABLED) {
    for (const pair<int, Variable> kv : from_qsx_col_) {
      std::cerr << kv.first << ": " << kv.second << "\n";
    }
  }
  return from_qsx_col_;
}

} // dlinear