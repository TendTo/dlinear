%{ /*** C/C++ Declarations ***/

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wold-style-cast"

#include <string>

#include "dlinear/mps/scanner.h"

/* import the parser's token type into a local typedef */
typedef dlinear::MpsParser::token token;
typedef dlinear::MpsParser::token_type token_type;

/* By default yylex returns int, we use token_type. Unfortunately yyterminate
 * by default returns 0, which is not of token_type. */
#define yyterminate() return token::END

/* This disables inclusion of unistd.h, which is not available under Visual C++
 * on Win32. The C++ scanner uses STL streams instead. */
#define YY_NO_UNISTD_H

// #define debug_print(__val__) std::cerr << __FILE__ << ":" << __LINE__ << " " << __val__ << std::endl;
#define debug_print(__val__) void(0)
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
int mps_yycolumn = 1;

#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = mps_yycolumn; yylloc->end.column = mps_yycolumn+yyleng-1; \
mps_yycolumn += yyleng;
%}

whitespace      [\x09 \xA0]
printable_char  [\x20-\x7E\xA0-xFF]
digit           [0-9]
hex             [0-9a-fA-F]
letter          [a-zA-Z]
comment         ^\*[^\n\r]*
rational        [-+]?([0-9]*\.?[0-9]+|[0-9]+\.?[0-9]*)([eE][-+]?[0-9]+)?
integer         [-+]?[0-9]+
special_char    [+\-/=%?!.$_~&^<>@*]
sym_begin       {letter}|{special_char}
sym_continue    {sym_begin}|{digit}
simple_symbol   {sym_begin}{sym_continue}*

/*** End of Declarations ***/

%x ROWS
%x COLUMNS
%x RHS
%x RANGES
%x BOUNDS

%% /*** Regular Expressions Part ***/

%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN - lexer rules ***/

{comment}[\n\r]+                { mps_yycolumn=1; }

(?i:NAME)                       { debug_print("name"); BEGIN(INITIAL); return token::NAME_DECLARATION; }
(?i:ROWS)                       { debug_print(yytext); BEGIN(ROWS); return token::ROWS_DECLARATION; }
(?i:COLUMNS)                    { debug_print(yytext); BEGIN(COLUMNS); return token::COLUMNS_DECLARATION; }
(?i:RHS)                        { debug_print(yytext); BEGIN(RHS); return token::RHS_DECLARATION; }
(?i:RANGES)                     { debug_print(yytext); BEGIN(RANGES); return token::RANGES_DECLARATION; }
(?i:BOUNDS)                     { debug_print(yytext); BEGIN(BOUNDS); return token::BOUNDS_DECLARATION; }
(?i:ENDATA)                     { debug_print(yytext); BEGIN(INITIAL); return token::ENDATA; }

<ROWS>^[ ]+[NELGnelg]           { debug_print("sense"); yylval->charVal = *yytext; return token::SENSE; }
<ROWS>[ ]+{simple_symbol}       { debug_print(yytext); yylval->stringVal = new std::string(yytext, yyleng); return token::SYMBOL; }
<ROWS>^[^ ]                     { debug_print("space"); BEGIN(INITIAL); yyless(0); }
<ROWS>\n+                       { debug_print("newline"); mps_yycolumn=1; return token::NEWLINE; }

<COLUMNS>[ ]+{rational}         { yylval->stringVal = new std::string(yytext, yyleng); return token::RATIONAL; }
<COLUMNS>[ ]+{simple_symbol}    { yylval->stringVal = new std::string(yytext, yyleng); return token::SYMBOL; }
<COLUMNS>^[^ ]                  { debug_print("space"); BEGIN(INITIAL); yyless(0); }
<COLUMNS>\n+                    { debug_print("newline"); mps_yycolumn=1; return token::NEWLINE; }

<RHS>[ ]+{rational}             { yylval->stringVal = new std::string(yytext, yyleng); return token::RATIONAL; }
<RHS>[ ]+{simple_symbol}        { yylval->stringVal = new std::string(yytext, yyleng); return token::SYMBOL; }
<RHS>^[^ ]                      { debug_print("space"); BEGIN(INITIAL); yyless(0); }
<RHS>\n+                        { debug_print("newline"); mps_yycolumn=1; return token::NEWLINE; }

<RANGES>[ ]+{rational}          { yylval->stringVal = new std::string(yytext, yyleng); return token::RATIONAL; }
<RANGES>[ ]+{simple_symbol}     { yylval->stringVal = new std::string(yytext, yyleng); return token::SYMBOL; }
<RANGES>^[^ ]                   { debug_print("space"); BEGIN(INITIAL); yyless(0); }
<RANGES>\n+                     { debug_print("newline"); mps_yycolumn=1; return token::NEWLINE; }

<BOUNDS>[ ]+(?i:LO|UP|FX|FR|MI|PL|BV|LI|UI|SC) { yylval->stringVal = new std::string(yytext, yyleng); return token::BOUND_TYPE; }
<BOUNDS>[ ]+{rational}          { yylval->stringVal = new std::string(yytext, yyleng); return token::RATIONAL; }
<BOUNDS>[ ]+{simple_symbol}     { yylval->stringVal = new std::string(yytext, yyleng); return token::SYMBOL; }
<BOUNDS>^[^ ]                   { debug_print("space"); BEGIN(INITIAL); yyless(0); }
<BOUNDS>\n+                     { debug_print("newline"); mps_yycolumn=1; return token::NEWLINE; }

{simple_symbol}                 {debug_print(yytext); yylval->stringVal = new std::string(yytext, yyleng); return token::SYMBOL; }

 /* gobble up white-spaces */
[ \t\r]+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    mps_yycolumn=1;
}

{integer} {
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

{rational} {
    yylval->rationalVal = new std::string(yytext, yyleng);
    return token::RATIONAL;
}
 
 /* pass all other characters up to bison */
. {
    debug_print("char");
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

#pragma GCC diagnostic pop
