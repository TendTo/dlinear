/**
 * @file Driver.h
 * @author dlinear
 * @date 15 Sep 2023
 * @copyright 2023 dlinear
 * @brief Driver form the parsing and execution of mps files.
 *
 * The driver puts in communication the parser and the scanner.
 * In the end, it produces a context that can be used to solve the
 * problem.
 */
#pragma once

#include <istream>
#include <map>
#include <string>
#include <unordered_map>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/mps/BoundType.h"
#include "dlinear/mps/Sense.h"
#include "dlinear/mps/scanner.h"
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
class MpsDriver {
 public:
  MpsDriver() = default;
  explicit MpsDriver(Context &context);  // NOLINT(runtime/references): Reference context filled during parsing.

  /**
   * Invoke the scanner and parser for a stream.
   * @param in	input stream
   * @param sname	stream name for error messages
   * @return		true if successfully parsed
   */
  bool parse_stream(std::istream &in, const std::string &sname = "stream input");

  /**
   * Invoke the scanner and parser on an input string.
   * @param input	input string
   * @param sname	stream name for error messages
   * @return		true if successfully parsed
   */
  bool parse_string(const std::string &input, const std::string &sname = "string stream");

  /**
   * Invoke the scanner and parser on a file. Use parse_stream with a
   * std::ifstream if detection of file reading errors is required.
   * @param filename	input file name
   * @return		true if successfully parsed
   */
  bool parse_file(const std::string &filename);

  /**
   * Error handling with associated line number. This can be modified to
   * output the error e.g. to a dialog box.
   */
  static void error(const location &l, const std::string &m);

  /**
   * General error handling. This can be modified to output the error
   * e.g. to a dialog box.
   */
  static void error(const std::string &m);

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
   *  <name>
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

  const std::string &stream_name() const { return stream_name_; }
  std::string &mutable_stream_name() { return stream_name_; }
  const std::string &problem_name() const { return problem_name_; }
  std::string &mutable_problem_name() { return problem_name_; }
  bool debug_scanning() const { return debug_scanning_; }
  void set_debug_scanning(bool b) { debug_scanning_ = b; }
  bool debug_parsing() const { return debug_parsing_; }
  void set_debug_parsing(bool b) { debug_parsing_ = b; }
  bool strict_mps() const { return strict_mps_; }
  void set_strict_mps(bool b) { strict_mps_ = b; }
  std::size_t n_assertions() const { return rhs_.size() + bounds_.size(); }
  bool is_min() const { return is_min_; }
  const std::string &obj_row() const { return obj_row_; }

  MpsScanner *scanner() { return scanner_; }

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

  std::string stream_name_;       ///< The name of the stream. It is either the name of the file or "stream input".
  std::string problem_name_;      ///< The name of the problem. Used to name the context.
  bool is_min_{true};             ///< True if the problem is a minimization problem.
  std::string obj_row_;           ///< The name of the objective row.
  MpsScanner *scanner_{nullptr};  ///< The scanner producing the tokens for the parser.
  bool strict_mps_{false};  ///< If true, the parser will check that all rhs, ranges and bounds have the same name.

  std::unordered_map<std::string, Sense> row_senses_;       ///< The sense of each row.
  std::unordered_map<std::string, Expression> rows_;        ///< The rows of the problem. Used to build the assertions.
  std::unordered_map<std::string, Variable> columns_;       ///< The columns of the problem. Contains the variables.
  std::unordered_map<std::string, bool> skip_lower_bound_;  ///< True if there is no need to manually add the lb 0 <= V.
  std::unordered_map<std::string, mpq_class> rhs_values_;   ///< The values of the hand side of the problem.

  // TODO(TendTo): Could be optimized by using unordered_map.
  std::map<std::string, Formula> rhs_;     ///< Assertions built by combining the rows and the rhs.
  std::map<std::string, Formula> bounds_;  ///< Assertions built by combining the columns and the bounds.

  std::string rhs_name_;    ///< The name of the first rhs found. Used if strict_mps_ is true.
  std::string bound_name_;  ///< The name of the first bound found. Used if strict_mps_ is true.

  Context &context_;  ///< The context filled during parsing of the expressions.

  bool debug_scanning_{false};  ///< If true, the scanner will print the scanning process.
  bool debug_parsing_{false};   ///< If true, the parser will print the parsing process.
};

}  // namespace dlinear::mps
