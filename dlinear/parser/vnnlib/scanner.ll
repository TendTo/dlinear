%{ /*** C/C++ Declarations ***/

#ifdef __clang__
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wdeprecated-register"
#pragma clang diagnostic ignored "-Wnull-conversion"
#pragma clang diagnostic ignored "-Wunneeded-internal-declaration"
#endif

/* ignore harmless bug in old versions of flex */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wold-style-cast"

#include <string>

#define __DLINEAR_VNNLIB_SCANNER_H__ // prevent inclusion of the flex header file two times
#include "dlinear/parser/vnnlib/scanner.h"
#undef __DLINEAR_VNNLIB_SCANNER_H__

/* import the parser's token type into a local typedef */
typedef dlinear::vnnlib::VnnlibParser::token token;
typedef dlinear::vnnlib::VnnlibParser::token_type token_type;

/* By default yylex returns int, we use token_type. Unfortunately yyterminate
 * by default returns 0, which is not of token_type. */
#define yyterminate() return token::END

/* This disables inclusion of unistd.h, which is not available under Visual C++
 * on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

/**
 * Flex expects the signature of yylex to be defined in the macro YY_DECL, and
 * the C++ parser expects it to be declared. We can factor both as follows.
 */
#undef YY_DECL
#define YY_DECL                                                          \
  dlinear::vnnlib::VnnlibParser::token_type dlinear::vnnlib::VnnlibScanner::lex( \
      dlinear::vnnlib::VnnlibParser::semantic_type *yylval, dlinear::vnnlib::VnnlibParser::location_type *yylloc)
%}

/*** Flex Declarations and Options ***/

/* enable c++ scanner class generation */
%option c++

/* change the name of the scanner class. results in "VnnlibFlexLexer" */
%option prefix="Vnnlib"

/* the manual says "somewhat more optimized" -
 * however, it also prevents interactive use */
%option batch

/* enable scanner to generate debug output. disable this for release
 * versions. */
%option debug

/* no support for include files is planned */
%option yywrap nounput

/* enables the use of start condition stacks */
%option stack

%option yylineno

/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
/* handle locations */
int vnnlib_yycolumn = 1;

#ifdef DLINEAR_PYDLINEAR
#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = vnnlib_yycolumn; yylloc->end.column = vnnlib_yycolumn+yyleng-1; \
vnnlib_yycolumn += yyleng; \
py_check_signals();
#elif !defined(NDEBUG)
#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = vnnlib_yycolumn; yylloc->end.column = vnnlib_yycolumn+yyleng-1; \
vnnlib_yycolumn += yyleng;
#else
#define YY_USER_ACTION void(0);
#endif
%}

whitespace      [\x09 \xA0]
printable_char  [\x20-\x7E\xA0-xFF]
digit           [0-9]
hex             [0-9a-fA-F]
letter          [a-zA-Z]
numeral         0|[1-9][0-9]*
decimal         {numeral}\.0*{numeral}
hexadecimal     "#x"[0-9A-Fa-f]+
binary          "#b"[01]+
special_char    [+\-/=%?!.$_~&^<>@*]
sym_begin       {letter}|{special_char}
sym_continue    {sym_begin}|{digit}
simple_symbol   {sym_begin}{sym_continue}*

/*** End of Declarations ***/

%x str
%x quoted

%% /*** Regular Expressions Part ***/

%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN - lexer rules ***/

";".* {
    vnnlib_yycolumn=1;
}

"!"                     { return VnnlibParser::token::TK_EXCLAMATION; }
"BINARY"                { return VnnlibParser::token::TK_BINARY; }
"DECIMAL"               { return VnnlibParser::token::TK_DECIMAL; }
"HEXADECIMAL"           { return VnnlibParser::token::TK_HEXADECIMAL; }
"NUMERAL"               { return VnnlibParser::token::TK_NUMERAL; }
"STRING"                { return VnnlibParser::token::TK_STRING; }
"_"                     { return VnnlibParser::token::TK_UNDERSCORE; }
"as"                    { return VnnlibParser::token::TK_AS; }
"exists"                { return VnnlibParser::token::TK_EXISTS; }
"forall"                { return VnnlibParser::token::TK_FORALL; }
"let"                   { return VnnlibParser::token::TK_LET; }
"par"                   { return VnnlibParser::token::TK_PAR; }

"assert"                { return VnnlibParser::token::TK_ASSERT; }
"check-sat"             { return VnnlibParser::token::TK_CHECK_SAT; }
"check-sat-assuming"    { return VnnlibParser::token::TK_CHECK_SAT_ASSUMING; }
"declare-const"         { return VnnlibParser::token::TK_DECLARE_CONST; }
"declare-fun"           { return VnnlibParser::token::TK_DECLARE_FUN; }
"declare-sort"          { return VnnlibParser::token::TK_DECLARE_SORT; }
"define-fun"            { return VnnlibParser::token::TK_DEFINE_FUN; }
"define-fun-rec"        { return VnnlibParser::token::TK_DEFINE_FUN_REC; }
"define-sort"           { return VnnlibParser::token::TK_DEFINE_SORT; }
"echo"                  { return VnnlibParser::token::TK_ECHO; }
"exit"                  { return VnnlibParser::token::TK_EXIT; }
"get-assertions"        { return VnnlibParser::token::TK_GET_ASSERTIONS; }
"get-assignment"        { return VnnlibParser::token::TK_GET_ASSIGNMENT; }
"get-info"              { return VnnlibParser::token::TK_GET_INFO; }
"get-model"             { return VnnlibParser::token::TK_GET_MODEL; }
"get-option"            { return VnnlibParser::token::TK_GET_OPTION; }
"get-proof"             { return VnnlibParser::token::TK_GET_PROOF; }
"get-unsat-assumptions" { return VnnlibParser::token::TK_GET_UNSAT_ASSUMPTIONS; }
"get-unsat-core"        { return VnnlibParser::token::TK_GET_UNSAT_CORE; }
"get-value"             { return VnnlibParser::token::TK_GET_VALUE; }
"pop"                   { return VnnlibParser::token::TK_POP; }
"push"                  { return VnnlibParser::token::TK_PUSH; }
"reset"                 { return VnnlibParser::token::TK_RESET; }
"reset-assertions"      { return VnnlibParser::token::TK_RESET_ASSERTIONS; }
"set-info"              { return VnnlibParser::token::TK_SET_INFO; }
"set-logic"             { return VnnlibParser::token::TK_SET_LOGIC; }
"set-option"            { return VnnlibParser::token::TK_SET_OPTION; }

"+"                     { return VnnlibParser::token::TK_PLUS; }
"-"                     { return VnnlibParser::token::TK_MINUS; }
"*"                     { return VnnlibParser::token::TK_TIMES; }
"/"                     { return VnnlibParser::token::TK_DIV; }
"="                     { return VnnlibParser::token::TK_EQ; }
"<="                    { return VnnlibParser::token::TK_LTE; }
">="                    { return VnnlibParser::token::TK_GTE; }
"<"                     { return VnnlibParser::token::TK_LT; }
">"                     { return VnnlibParser::token::TK_GT; }
"exp"                   { return VnnlibParser::token::TK_EXP; }
"log"                   { return VnnlibParser::token::TK_LOG; }
"abs"                   { return VnnlibParser::token::TK_ABS; }
"sin"                   { return VnnlibParser::token::TK_SIN; }
"cos"                   { return VnnlibParser::token::TK_COS; }
"tan"                   { return VnnlibParser::token::TK_TAN; }
"asin"|"arcsin"         { return VnnlibParser::token::TK_ASIN; }
"acos"|"arccos"         { return VnnlibParser::token::TK_ACOS; }
"atan"|"arctan"         { return VnnlibParser::token::TK_ATAN; }
"atan2"|"arctan2"       { return VnnlibParser::token::TK_ATAN2; }
"sinh"                  { return VnnlibParser::token::TK_SINH; }
"cosh"                  { return VnnlibParser::token::TK_COSH; }
"tanh"                  { return VnnlibParser::token::TK_TANH; }
"min"                   { return VnnlibParser::token::TK_MIN; }
"max"                   { return VnnlibParser::token::TK_MAX; }
"maximize"              { return VnnlibParser::token::TK_MAXIMIZE; }
"minimize"              { return VnnlibParser::token::TK_MINIMIZE; }
"sqrt"                  { return VnnlibParser::token::TK_SQRT; }
"^"|"pow"               { return VnnlibParser::token::TK_POW; }

"true"                  { return VnnlibParser::token::TK_TRUE; }
"false"                 { return VnnlibParser::token::TK_FALSE; }
"and"                   { return VnnlibParser::token::TK_AND; }
"or"                    { return VnnlibParser::token::TK_OR; }
"xor"                   { return VnnlibParser::token::TK_XOR; }
"not"                   { return VnnlibParser::token::TK_NOT; }
"ite"                   { return VnnlibParser::token::TK_ITE; }
"=>"                    { return VnnlibParser::token::TK_IMPLIES; }

 /* gobble up white-spaces */
[ \t\r]+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    vnnlib_yycolumn=1;
}

[-+]?(0|[1-9][0-9]*) {
    try {
        static_assert(sizeof(std::int64_t) == sizeof(long), "sizeof(std::int64_t) != sizeof(long).");
        yylval->emplace<int64_t>(std::stol(yytext));
        return token::INT;
    } catch(std::out_of_range& e) {
        std::cerr << "At line " << yylloc->begin.line
                  << " the following value would fall out of the range of the result type (long):\n"
                  << yytext << "\n";
        throw e;
    }
}

[-+]?((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?)   {
    yylval->emplace<std::string>(yytext, yyleng);
    return token::RATIONAL;
}

[-+]?((([0-9]+)|([0-9]+\.)))                            {
    yylval->emplace<std::string>(yytext, yyleng);
    return token::RATIONAL;
}

[-+]?0[xX]({hex}+\.?|{hex}*\.{hex}+)([pP][-+]?[0-9]+)? {
    yylval->emplace<double>(std::stod(yytext));
    return token::HEXFLOAT;
}

{simple_symbol} {
    yylval->emplace<std::string>(yytext, yyleng);
    return token::SYMBOL;
}

":"{simple_symbol} {
    yylval->emplace<std::string>(yytext, yyleng);
    return token::KEYWORD;
}

\"                      { BEGIN str; yymore(); }
<str>\"\"               { yymore(); }
<str>[\n\r]+            { yymore(); }
<str>\"                 {
    BEGIN 0;
    yylval->emplace<std::string>(yytext, yyleng);
    return token::STRING;
}
<str>.                  { yymore(); }

\|                      { BEGIN quoted; yymore(); }
<quoted>[\n\r]+         { yymore(); }
<quoted>\|              {
    BEGIN 0;
    yylval->emplace<std::string>(yytext, yyleng);
    return token::SYMBOL;
}
<quoted>\\              { }
<quoted>.               { yymore(); }

 /* pass all other characters up to bison */
. {
    return static_cast<token_type>(*yytext);
}

%% /*** Additional Code ***/

namespace dlinear::vnnlib {

VnnlibScanner::VnnlibScanner(std::istream* in, std::ostream* out) : VnnlibFlexLexer(in, out) {}

VnnlibScanner::~VnnlibScanner() {}

void VnnlibScanner::set_debug(const bool b) {
    yy_flex_debug = b;
}
}  // namespace dlinear::vnnlib

/* This implementation of VnnlibFlexLexer::yylex() is required to fill the
 * vtable of the class VnnlibFlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the VnnlibScanner class instead. */

#ifdef yylex
#undef yylex
#endif

int VnnlibFlexLexer::yylex()
{
    std::cerr << "in VnnliblexLexer::yylex() !" << std::endl;
    return 0;
}

/* When the scanner receives an end-of-file indication from YY_INPUT, it then
 * checks the yywrap() function. If yywrap() returns false (zero), then it is
 * assumed that the function has gone ahead and set up `yyin' to point to
 * another input file, and scanning continues. If it returns true (non-zero),
 * then the scanner terminates, returning 0 to its caller. */

int VnnlibFlexLexer::yywrap()
{
    return 1;
}

#pragma GCC diagnostic pop

#ifdef __clang__
#pragma clang diagnostic pop
#endif
