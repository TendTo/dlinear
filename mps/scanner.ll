%{ /*** C/C++ Declarations ***/

#include <string>

#include "scanner.h"

/* import the parser's token type into a local typedef */
typedef dlinear::MpsParser::token token;
typedef dlinear::MpsParser::token_type token_type;

/* By default yylex returns int, we use token_type. Unfortunately yyterminate
 * by default returns 0, which is not of token_type. */
#define yyterminate() return token::END

/* This disables inclusion of unistd.h, which is not available under Visual C++
 * on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

%}

/*** Flex Declarations and Options ***/

/* enable c++ scanner class generation */
%option c++

/* change the name of the scanner class. results in "MpsFlexLexer" */
%option prefix="Mps"

/* the manual says "somewhat more optimized" -
 * however, it also prevents interactive use */
/* %option batch */

/* enable scanner to generate debug output. disable this for release
 * versions. */
%option debug

/* no support for include files is planned */
%option noyywrap nounput

/* enables the use of start condition stacks */
%option stack

%option yylineno

/* The following paragraph suffices to track locations accurately. Each time
 * yylex is invoked, the begin position is moved onto the end position. */
%{
/* handle locations */
int smt2_yycolumn = 1;

#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = smt2_yycolumn; yylloc->end.column = smt2_yycolumn+yyleng-1; \
smt2_yycolumn += yyleng;
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
%x ROWS
%x COLUMNS


%% /*** Regular Expressions Part ***/

%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN - lexer rules ***/

";".*[\n\r]+ {
    smt2_yycolumn=1;
}

"NAME"                  { return MmpParser::token::TK_PROB_NAME; }
"!"                     { return MpsParser::token::TK_EXCLAMATION; }
"BINARY"                { return MpsParser::token::TK_BINARY; }
"DECIMAL"               { return MpsParser::token::TK_DECIMAL; }
"HEXADECIMAL"           { return MpsParser::token::TK_HEXADECIMAL; }
"NUMERAL"               { return MpsParser::token::TK_NUMERAL; }
"STRING"                { return MpsParser::token::TK_STRING; }
"_"                     { return MpsParser::token::TK_UNDERSCORE; }
"as"                    { return MpsParser::token::TK_AS; }
"exists"                { return MpsParser::token::TK_EXISTS; }
"forall"                { return MpsParser::token::TK_FORALL; }
"let"                   { return MpsParser::token::TK_LET; }
"par"                   { return MpsParser::token::TK_PAR; }

"assert"                { return MpsParser::token::TK_ASSERT; }
"check-sat"             { return MpsParser::token::TK_CHECK_SAT; }
"check-sat-assuming"    { return MpsParser::token::TK_CHECK_SAT_ASSUMING; }
"declare-const"         { return MpsParser::token::TK_DECLARE_CONST; }
"declare-fun"           { return MpsParser::token::TK_DECLARE_FUN; }
"declare-sort"          { return MpsParser::token::TK_DECLARE_SORT; }
"define-fun"            { return MpsParser::token::TK_DEFINE_FUN; }
"define-fun-rec"        { return MpsParser::token::TK_DEFINE_FUN_REC; }
"define-sort"           { return MpsParser::token::TK_DEFINE_SORT; }
"echo"                  { return MpsParser::token::TK_ECHO; }
"exit"                  { return MpsParser::token::TK_EXIT; }
"get-assertions"        { return MpsParser::token::TK_GET_ASSERTIONS; }
"get-assignment"        { return MpsParser::token::TK_GET_ASSIGNMENT; }
"get-info"              { return MpsParser::token::TK_GET_INFO; }
"get-model"             { return MpsParser::token::TK_GET_MODEL; }
"get-option"            { return MpsParser::token::TK_GET_OPTION; }
"get-proof"             { return MpsParser::token::TK_GET_PROOF; }
"get-unsat-assumptions" { return MpsParser::token::TK_GET_UNSAT_ASSUMPTIONS; }
"get-unsat-core"        { return MpsParser::token::TK_GET_UNSAT_CORE; }
"get-value"             { return MpsParser::token::TK_GET_VALUE; }
"pop"                   { return MpsParser::token::TK_POP; }
"push"                  { return MpsParser::token::TK_PUSH; }
"reset"                 { return MpsParser::token::TK_RESET; }
"reset-assertions"      { return MpsParser::token::TK_RESET_ASSERTIONS; }
"set-info"              { return MpsParser::token::TK_SET_INFO; }
"set-logic"             { return MpsParser::token::TK_SET_LOGIC; }
"set-option"            { return MpsParser::token::TK_SET_OPTION; }

"+"                     { return MpsParser::token::TK_PLUS; }
"-"                     { return MpsParser::token::TK_MINUS; }
"*"                     { return MpsParser::token::TK_TIMES; }
"/"                     { return MpsParser::token::TK_DIV; }
"="                     { return MpsParser::token::TK_EQ; }
"<="                    { return MpsParser::token::TK_LTE; }
">="                    { return MpsParser::token::TK_GTE; }
"<"                     { return MpsParser::token::TK_LT; }
">"                     { return MpsParser::token::TK_GT; }
"exp"                   { return MpsParser::token::TK_EXP; }
"log"                   { return MpsParser::token::TK_LOG; }
"abs"                   { return MpsParser::token::TK_ABS; }
"sin"                   { return MpsParser::token::TK_SIN; }
"cos"                   { return MpsParser::token::TK_COS; }
"tan"                   { return MpsParser::token::TK_TAN; }
"asin"|"arcsin"         { return MpsParser::token::TK_ASIN; }
"acos"|"arccos"         { return MpsParser::token::TK_ACOS; }
"atan"|"arctan"         { return MpsParser::token::TK_ATAN; }
"atan2"|"arctan2"       { return MpsParser::token::TK_ATAN2; }
"sinh"                  { return MpsParser::token::TK_SINH; }
"cosh"                  { return MpsParser::token::TK_COSH; }
"tanh"                  { return MpsParser::token::TK_TANH; }
"min"                   { return MpsParser::token::TK_MIN; }
"max"                   { return MpsParser::token::TK_MAX; }
"maximize"              { return MpsParser::token::TK_MAXIMIZE; }
"minimize"              { return MpsParser::token::TK_MINIMIZE; }
"sqrt"                  { return MpsParser::token::TK_SQRT; }
"^"|"pow"               { return MpsParser::token::TK_POW; }

"true"                  { return MpsParser::token::TK_TRUE; }
"false"                 { return MpsParser::token::TK_FALSE; }
"and"                   { return MpsParser::token::TK_AND; }
"or"                    { return MpsParser::token::TK_OR; }
"xor"                   { return MpsParser::token::TK_XOR; }
"not"                   { return MpsParser::token::TK_NOT; }
"ite"                   { return MpsParser::token::TK_ITE; }
"=>"                    { return MpsParser::token::TK_IMPLIES; }

 /* gobble up white-spaces */
[ \t\r]+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    smt2_yycolumn=1;
}

[-+]?(0|[1-9][0-9]*) {
    try {
        static_assert(sizeof(int64_t) == sizeof(long), "sizeof(std::int64_t) != sizeof(long).");
        yylval->int64Val = std::stol(yytext);
        return token::INT;
    } catch(std::out_of_range& e) {
        std::cerr << "At line " << yylloc->begin.line
                  << " the following value would fall out of the range of the result type (long):\n"
                  << yytext << "\n";
        throw e;
    }
}

[-+]?((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?)   {
    yylval->rationalVal = new std::string(yytext, yyleng);
    return token::RATIONAL;
}

[-+]?((([0-9]+)|([0-9]+\.)))                            {
    yylval->rationalVal = new std::string(yytext, yyleng);
    return token::RATIONAL;
}

[-+]?0[xX]({hex}+\.?|{hex}*\.{hex}+)([pP][-+]?[0-9]+)? {
    yylval->hexfloatVal = std::stod(yytext);
    return token::HEXFLOAT;
}

{simple_symbol} {
    yylval->stringVal = new std::string(yytext, yyleng);
    return token::SYMBOL;
}

":"{simple_symbol} {
    yylval->stringVal = new std::string(yytext, yyleng);;
    return token::KEYWORD;
}

\"                      { BEGIN str; yymore(); }
<str>\"\"               { yymore(); }
<str>[\n\r]+            { yymore(); }
<str>\"                 {
    BEGIN 0;
    yylval->stringVal = new std::string(yytext, yyleng);;
    return token::STRING;
}
<str>.                  { yymore(); }

\|                      { BEGIN quoted; yymore(); }
<quoted>[\n\r]+         { yymore(); }
<quoted>\|              {
    BEGIN 0;
    yylval->stringVal = new std::string(yytext, yyleng);;
    return token::SYMBOL;
}
<quoted>\\              { }
<quoted>.               { yymore(); }

 /* pass all other characters up to bison */
. {
    return static_cast<token_type>(*yytext);
}

%% /*** Additional Code ***/

namespace dlinear {

MpsScanner::MpsScanner(std::istream* in, std::ostream* out) : MpsFlexLexer(in, out) {}

MpsScanner::~MpsScanner() {}

void MpsScanner::set_debug(const bool b) {
    yy_flex_debug = b;
}
}  // namespace dlinear

/* This implementation of MpsFlexLexer::yylex() is required to fill the
 * vtable of the class MpsFlexLexer. We define the scanner's main yylex
 * function via YY_DECL to reside in the MpsScanner class instead. */

#ifdef yylex
#undef yylex
#endif

int MpsFlexLexer::yylex()
{
    std::cerr << "in MpslexLexer::yylex() !" << std::endl;
    return 0;
}
