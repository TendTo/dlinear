/**
 * @file scanner.h
 * @author dlinear
 * @date 22 Aug 2023
 * @copyright 2023 dlinear
 * @brief Scanner utility class.
 *
 * This class extends from the Smt2FlexLexer class generated by Flex. It
 * provides a class named Smt2Scanner used to parse the file using the Flex
 * API.
 */
#ifndef DLINEAR_SMT2_SCANNER_H_
#define DLINEAR_SMT2_SCANNER_H_

// Flex expects the signature of yylex to be defined in the macro YY_DECL, and
// the C++ parser expects it to be declared. We can factor both as follows.

#ifndef YY_DECL

#define YY_DECL                                              \
  dlinear::Smt2Parser::token_type dlinear::Smt2Scanner::lex( \
      dlinear::Smt2Parser::semantic_type *yylval,            \
      dlinear::Smt2Parser::location_type *yylloc)
#endif

#ifndef __FLEX_LEXER_H
#define yyFlexLexer Smt2FlexLexer
#include <FlexLexer.h>
#undef yyFlexLexer
#endif

// The following include should come first before parser.yy.hh.
// Do not alpha-sort them.
#include "dlinear/smt2/sort.h"
#include "dlinear/smt2/Term.h"
#include "dlinear/symbolic/symbolic.h"
#include "dlinear/util/Box.h"
#include "dlinear/smt2/parser.yy.hpp"

namespace dlinear {

/**
 * Smt2Scanner is a derived class to add some extra function to the scanner
 * class. Flex itself creates a class named yyFlexLexer, which is renamed using
 * macros to ExampleFlexLexer. However we change the context of the generated
 * yylex() function to be contained within the Smt2Scanner class. This is
 * required because the yylex() defined in ExampleFlexLexer has no parameters.
 */
class Smt2Scanner : public Smt2FlexLexer {
 public:
  /**
   * Create a new scanner object. The streams arg_yyin and arg_yyout default
   * to cin and cout, but that assignment is only made when initializing in
   * yylex().
   */
  explicit Smt2Scanner(std::istream *arg_yyin = nullptr, std::ostream *arg_yyout = nullptr);

  Smt2Scanner(const Smt2Scanner &) = delete;
  Smt2Scanner(Smt2Scanner &&) = delete;
  Smt2Scanner &operator=(const Smt2Scanner &) = delete;
  Smt2Scanner &operator=(Smt2Scanner &&) = delete;

  /** Required for virtual functions */
  ~Smt2Scanner() override;

  /**
   * This is the main lexing function. It is generated by flex according to
   * the macro declaration YY_DECL above. The generated bison parser then
   * calls this virtual function to fetch new tokens.
   */
  virtual Smt2Parser::token_type lex(Smt2Parser::semantic_type *yylval, Smt2Parser::location_type *yylloc);

  /** Enable debug output (via arg_yyout) if compiled into the scanner. */
  void set_debug(bool b);
};

} // namespace dlinear

#endif // DLINEAR_SMT2_SCANNER_H_