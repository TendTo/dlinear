/**
 * @author Ernesto Casablanca (casablancaernesto@gmail.com)
 * @copyright 2024 dlinear
 * @licence BSD 3-Clause License
 * Driver for the parsing and execution of mps files.
 *
 * The driver puts in communication the parser and the scanner.
 * In the end, it produces a context that can be used to solve the problem.
 */
#pragma once

#include <istream>
#include <map>
#include <string>
#include <unordered_map>
#include <utility>

#include "dlinear/libs/libgmp.h"
#include "dlinear/parser/Driver.h"
#include "dlinear/parser/mps/BoundType.h"
#include "dlinear/parser/mps/Sense.h"
#include "dlinear/parser/mps/scanner.h"
#include "dlinear/solver/Context.h"
#include "dlinear/symbolic/symbolic.h"

namespace dlinear::mps {

/**
 * The MpsDriver class brings together all components. It creates an
 * instance of the Parser and Scanner classes and connects them. Then
 * the input stream is fed into the scanner object and the parser gets
 * it's token sequence. Furthermore the driver object is available in
 * the grammar rules as a parameter. Therefore the driver class
 * contains a reference to the structure into which the parsed data is
 * saved.
 */
class MpsDriver : public Driver {
 public:
  explicit MpsDriver(Context &context);

  bool ParseStreamCore(std::istream &in) override;

  /**
   * Error handling with associated line number. This can be modified to
   * output the error e.g. to a dialog box.
   */
  static void error(const location &l, const std::string &m);

  /**
   * Set the objective sense of the problem after having encountered the
   * OBJSENSE section.
   *
   * In the mps file, the objective sense is defined by:
   *
   * OBJSENSE
   *  MAX or MIN
   * @param is_min whether the problem is a minimization problem. It is true by default.
   */
  void ObjectiveSense(bool is_min);

  /**
   * Set the name of the objective row after having encountered the
   * OBJNAME section.
   *
   * In the mps file, the objective name is defined by:
   *
   * OBJNAME
   *   name
   * @param row name of the objective row
   */
  void ObjectiveName(const std::string &row);

  /**
   * Add a row to the problem.
   * It creates a record for the row and stores the sense.
   * In the mps file, a row is defined by:
   *
   *    | Field1 | Field2 | Field3 | Field4 | Field5 | Field6 |
   *    |--------|--------|--------|--------|--------|--------|
   *    | Sense  | Row    |        |        |        |        |
   *
   * @param sense relation between the row and the rhs
   * @param row identifier of the row
   */
  void AddRow(Sense sense, const std::string &row);

  /**
   * Add a column to the problem.
   * It creates a the variable (column), if not already present, and adds its
   * coefficient (value) to the row.
   * In the mps file, a row is defined by:
   *
   *    | Field1 | Field2 | Field3 | Field4      | Field5 | Field6      |
   *    |--------|--------|--------|-------------|--------|-------------|
   *    |        | Column | Row1   | Value(Row1) | Row2   | Value(Row2) |
   *
   * The last two fields are optional.
   * @param column identifier of the column (variable)
   * @param row identifier of the row
   * @param value coefficient of the column in the row
   */
  void AddColumn(const std::string &column, const std::string &row, mpq_class value);

  /**
   * Add the right hand side of the row.
   * It creates a formula that combines the row and the rhs
   * using the sense of the row.
   * If strict_mps_ is true and multiple rhs are found,
   * only the first one is considered, the others are skipped.
   * In the mps file, an RHS line is defined by:
   *
   *    | Field1 | Field2 | Field3 | Field4       | Field5 | Field6       |
   *    |--------|--------|--------|--------------|--------|--------------|
   *    |        | RHS    | Row1   | Value (Row1) | Row2   | Value (Row2) |
   *
   * The last two fields are optional.
   * @param rhs identifier of the rhs. Used if strict_mps_ is true.
   * @param row identifier of the row
   * @param value rhs value
   */
  void AddRhs(const std::string &rhs, const std::string &row, mpq_class value);

  /**
   * Add a new row contraint based on the range.
   * If strict_mps_ is true and multiple ranges are found,
   * only the first one is considered, the others are skipped.
   * In the mps file, a range line is defined by:
   *
   *    | Field1 | Field2 | Field3 | Field4       | Field5 | Field6       |
   *    |--------|--------|--------|--------------|--------|--------------|
   *    |        | Rhs    | Row1   | Value (Row1) | Row2   | Value (Row2) |
   *
   * The last two fields are optional.
   * The behaviour depends on the sense of the row:
   *
   *    | Row type | Range sign | Lower rhs | Upper rhs |
   *    |----------|------------|-----------|-----------|
   *    | G        | +/-        | rhs       | rhs + |r| |
   *    | L        | +/-        | rhs - |r| | rhs       |
   *    | E        | +          | rhs       | rhs + r   |
   *    | E        | -          | rhs + r   | rhs       |
   *
   * @param rhs identifier of the rhs. Used if strict_mps_ is true.
   * @param row identifier of the row
   * @param value range value
   */
  void AddRange(const std::string &rhs, const std::string &row, mpq_class value);

  /**
   * Add a bound to a variable (column).
   * If strict_mps_ is true and multiple bounds are found,
   * only the first one is considered, the others are skipped.
   * In the mps file, a bound line is defined by:
   *
   *   | Field1     | Field2 | Field3 | Field4 | Field5 | Field6 |
   *   |------------|--------|--------|--------|--------|--------|
   *   | Bound Type | Bound  | Column | Value  |        |        |
   *
   * @param type bound type
   * @param bound identifier of the bound. Used if strict_mps_ is true.
   * @param column identifier of the variable (column)
   * @param value bound value
   */
  void AddBound(BoundType type, const std::string &bound, const std::string &column, mpq_class value);

  /**
   * Add a binary bound to a variable (column).
   * The value is not present, for it is inferred from the bound type.
   * If strict_mps_ is true and multiple bounds are found,
   * only the first one is considered, the others are skipped.
   * In the mps file, a bound line is defined by:
   *
   *   | Field1     | Field2 | Field3 | Field4 | Field5 | Field6 |
   *   |------------|--------|--------|--------|--------|--------|
   *   | Bound Type | Bound  | Column |        |        |        |
   *
   * @param type bound type. Must be either BV, FR, MI or PL.
   * @param bound identifier of the bound. Used if strict_mps_ is true.
   * @param column identifier of the variable (column)
   */
  void AddBound(BoundType type, const std::string &bound, const std::string &column);

  /**
   * Called when the parser has reached the ENDATA section.
   * It finalizes the assertions, adding the default lower bound
   * if needed, and launches the solver.
   */
  void End();

  /** @getter{problem_name, MpsDriver} */
  [[nodiscard]] const std::string &problem_name() const { return problem_name_; }
  /** @getsetter{problem_name, MpsDriver} */
  std::string &m_problem_name() { return problem_name_; }
  /** @checker{enabled, strict mps} */
  [[nodiscard]] bool strict_mps() const { return strict_mps_; }
  /**
   * Set the strict mps mode.
   * @param b new value of the strict mps mode
   */
  void set_strict_mps(bool b) { strict_mps_ = b; }
  /** @getter{number of assertions, MpsDriver} */
  [[nodiscard]] std::size_t n_assertions() const { return rhs_.size() + bounds_.size(); }
  /** @checker{enabled, minimization} */
  [[nodiscard]] bool is_min() const { return is_min_; }
  /** @getter{objective row name, MpsDriver} */
  [[nodiscard]] const std::string &obj_row() const { return obj_row_; }
  /** @getter{scanner, MpsDriver} */
  [[nodiscard]] MpsScanner *scanner() { return scanner_; }

  /**
   * Print the problem in the smt2 format.
   * @param os output stream
   */
  void ToSmt2(std::ostream &os) const;

 private:
  /**
   * If strict_mps_ is true, keeps track of the name of the first rhs found.
   * All the other rhs must have the same name, otherwise they are skipped.
   * @param rhs identifier of the rhs
   * @return whether the rhs should be considered
   */
  inline bool VerifyStrictRhs(const std::string &rhs);

  /**
   * If strict_mps_ is true, keeps track of the name of the first bound found.
   * All the other bound must have the same name, otherwise they are skipped.
   * @param bound identifier of the bound
   * @return whether the bound should be considered
   */
  inline bool VerifyStrictBound(const std::string &bound);

  std::string problem_name_;      ///< The name of the problem. Used to name the context.
  bool is_min_{true};             ///< True if the problem is a minimization problem.
  std::string obj_row_;           ///< The name of the objective row.
  MpsScanner *scanner_{nullptr};  ///< The scanner producing the tokens for the parser.
  bool strict_mps_{false};  ///< If true, the parser will check that all rhs, ranges and bounds have the same name.

  /**
   * The rows of the problem. Contains a map between each variable, stored as an expression, and the
   * coefficient. It will be used to build the final row_expression using the ExpressionAddFactory class.
   * The result is then combined with the rhs value and the correct row sense to build the Formula that makes up the
   * assertion.
   */
  std::unordered_map<std::string, std::map<Expression, mpq_class>> rows_;
  std::unordered_map<std::string, Sense> row_senses_;       ///< The sense of each row.
  std::unordered_map<std::string, Variable> columns_;       ///< The columns of the problem. Contains the variables.
  std::unordered_map<std::string, bool> skip_lower_bound_;  ///< True if there is no need to manually add the lb 0 <= V.
  std::unordered_map<std::string, mpq_class> rhs_values_;   ///< The values of the hand side of the problem.

  // TODO(TendTo): Could be optimized by using unordered_map.
  std::map<std::string, Formula> rhs_;     ///< Assertions built by combining the rows and the rhs.
  std::map<std::string, Formula> bounds_;  ///< Assertions built by combining the columns and the bounds.

  std::string rhs_name_;    ///< The name of the first rhs found. Used if strict_mps_ is true.
  std::string bound_name_;  ///< The name of the first bound found. Used if strict_mps_ is true.
};

}  // namespace dlinear::mps
