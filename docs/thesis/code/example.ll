%{ /*** C/C++ Declarations ***/
#include "dlinear/smt2/scanner.h"
typedef dlinear::Smt2Parser::token token;
typedef dlinear::Smt2Parser::token_type token_type;
%}

/*** Flex Declarations and Options ***/
digit           [0-9]
letter          [a-zA-Z]

%% /*** Lexer rules ***/
"check-sat"     { return Smt2Parser::token::TK_CHECK_SAT; }

%% /*** Additional Code ***/
namespace dlinear {
Smt2Scanner::Smt2Scanner(std::istream* in, std::ostream* out) : Smt2FlexLexer(in, out) {}
} /*** End of Namespace ***/
