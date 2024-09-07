/**
 * @file scanner.h
 * @author dlinear
 * @date 15 Sep 2023
 * @copyright 2023 dlinear
 * @brief Scanner utility class.
 *
 * This class extends from the MpsFlexLexer class generated by Flex. It
 * provides a class named MpsScanner used to parse the file using the Flex
 * API.
 */
#pragma once

#include <iosfwd>

#ifndef __DLINEAR_MPS_SCANNER_H__
#define yyFlexLexer MpsFlexLexer
#include <FlexLexer.h>
#undef yyFlexLexer
#endif

#ifdef DLINEAR_PYDLINEAR
#include "dlinear/util/SignalHandlerGuard.h"
#include "dlinear/util/interrupt.h"
#endif

#include "dlinear/parser/mps/BoundType.h"
#include "dlinear/parser/mps/Sense.h"
// All the types needed for the scanner to work must be imported before parser.yy.hh.
// Needs to be included after the above headers.
#include "dlinear/parser/mps/parser.yy.hpp"

namespace dlinear::mps {

/**
 * MpsScanner is a derived class to add some extra function to the scanner
 * class. Flex itself creates a class named yyFlexLexer, which is renamed using
 * macros to ExampleFlexLexer. However we change the context of the generated
 * yylex() function to be contained within the MpsScanner class. This is
 * required because the yylex() defined in ExampleFlexLexer has no parameters.
 */
class MpsScanner : public MpsFlexLexer {
 public:
  /**
   * Create a new scanner object. The streams arg_yyin and arg_yyout default
   * to cin and cout, but that assignment is only made when initializing in
   * yylex().
   */
  explicit MpsScanner(std::istream *arg_yyin = nullptr, std::ostream *arg_yyout = nullptr);

  MpsScanner(const MpsScanner &) = delete;
  MpsScanner(MpsScanner &&) = delete;
  MpsScanner &operator=(const MpsScanner &) = delete;
  MpsScanner &operator=(MpsScanner &&) = delete;

  /** Required for virtual functions */
  ~MpsScanner() override;

  /**
   * This is the main lexing function. It is generated by flex according to
   * the macro declaration YY_DECL above. The generated bison parser then
   * calls this virtual function to fetch new tokens.
   */
  virtual MpsParser::token_type lex(MpsParser::semantic_type *yylval, MpsParser::location_type *yylloc);

  /** Enable debug output (via arg_yyout) if compiled into the scanner. */
  void set_debug(bool b);

 private:
#ifdef DLINEAR_PYDLINEAR
  SignalHandlerGuard guard{SIGINT, interrupt_handler, &g_interrupted};
#endif
};

}  // namespace dlinear::mps
