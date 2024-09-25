%{ /*** C/C++ Declarations ***/

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wsign-compare"
#pragma GCC diagnostic ignored "-Wold-style-cast"

#include <string>

#define __DLINEAR_MPS_SCANNER_H__ // prevent inclusion of the flex header two times
#include "dlinear/parser/mps/scanner.h"
#undef __DLINEAR_MPS_SCANNER_H__

#include "dlinear/parser/mps/Sense.h"
#include "dlinear/parser/mps/BoundType.h"

/* import the parser's token type into a local typedef */
typedef dlinear::mps::MpsParser::token token;
typedef dlinear::mps::MpsParser::token_type token_type;

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
#define YY_DECL                                                                                                     \
  dlinear::mps::MpsParser::token_type dlinear::mps::MpsScanner::lex(dlinear::mps::MpsParser::semantic_type *yylval, \
                                                                    dlinear::mps::MpsParser::location_type *yylloc)
%}

/*** Flex Declarations and Options ***/

/* enable c++ scanner class generation */
%option c++

/* change the name of the scanner class. results in "MpsFlexLexer" */
%option prefix="Mps"

/* the manual says "somewhat more optimized" -
 * however, it also prevents interactive use */
%option batch

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

#ifdef DLINEAR_PYDLINEAR
#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = mps_yycolumn; yylloc->end.column = mps_yycolumn+yyleng-1; \
mps_yycolumn += yyleng; \
py_check_signals();
#elif !defined(NDEBUG)
#define YY_USER_ACTION yylloc->begin.line = yylloc->end.line = yylineno; \
yylloc->begin.column = mps_yycolumn; yylloc->end.column = mps_yycolumn+yyleng-1; \
mps_yycolumn += yyleng;
#else
#define YY_USER_ACTION void(0);
#endif

%}

whitespace      [ \t\r]
comment_start   ^\*
comment         {comment_start}[^\n\r]*
symbol          [^ \t\r\n'"]+
rational        [-+]?((([0-9]+)|([0-9]*\.?[0-9]+))([eE][-+]?[0-9]+)?) 

/*** End of Declarations ***/

%x NAME_SECTION
%x COMMENT
%x COMMAND

%% /*** Regular Expressions Part ***/

%{
    // reset location
    yylloc->step();
%}

 /*** BEGIN - lexer rules ***/

{comment_start}{whitespace}*"@set-info"{whitespace}   { BEGIN(COMMAND); return token::SET_INFO; }
{comment_start}{whitespace}*"@set-option"{whitespace} { BEGIN(COMMAND); return token::SET_OPTION; }

<COMMAND>{rational}             { yylval->emplace<std::string>(yytext, yyleng); return token::RATIONAL; }
<COMMAND>{symbol}               { yylval->emplace<std::string>(yytext, yyleng); return token::SYMBOL; }
<COMMAND>{whitespace}+          {  }
<COMMAND>[\n]                   { BEGIN(INITIAL); return static_cast<token_type>(*yytext); }

{comment_start}                 { BEGIN(COMMENT); }
<COMMENT>[^\n\r]*               { }
<COMMENT>[\n]                   { BEGIN(INITIAL); }

(?i:NAME)                       { BEGIN(NAME_SECTION); return token::NAME_DECLARATION; }
(?i:ROWS)                       { return token::ROWS_DECLARATION; }
(?i:COLUMNS)                    { return token::COLUMNS_DECLARATION; }
(?i:RHS)                        { return token::RHS_DECLARATION; }
(?i:RANGES)                     { return token::RANGES_DECLARATION; }
(?i:BOUNDS)                     { return token::BOUNDS_DECLARATION; }
(?i:OBJSENSE)                   { return token::OBJSENSE_DECLARATION; }
(?i:OBJNAME)                    { return token::OBJNAME_DECLARATION; }
(?i:ENDATA)                     { return token::ENDATA; }

{whitespace}+(?i:MAX)                { return token::MAX; }
{whitespace}+(?i:MIN)                { return token::MIN; }
{whitespace}+[NELGnelg]              { yylval->emplace<Sense>(ParseSense(yytext)); return token::SENSE; }
{whitespace}+(?i:BV|MI|PL|FR)        { yylval->emplace<BoundType>(ParseBoundType(yytext)); return token::BOUND_TYPE_SINGLE; }
{whitespace}+(?i:LO|UP|FX|LI|UI|SC)  { yylval->emplace<BoundType>(ParseBoundType(yytext)); return token::BOUND_TYPE; }

{whitespace}+{symbol}           {
                                    const char* symbol = yytext;
                                    size_t len = yyleng;
                                    while (*symbol == ' ') { // skip leading spaces
                                        ++symbol; 
                                        --len;
                                    }
                                    yylval->emplace<std::string>(symbol, len);
                                    return token::SYMBOL;
                                }

['"]{symbol}['"]                { 
                                    yylval->emplace<std::string>(yytext+1, yyleng-2);
                                    return token::QUOTED_SYMBOL;
                                }

<NAME_SECTION>[^ \r\t\n]+             { yylval->emplace<std::string>(yytext, yyleng); return token::SYMBOL; }
<NAME_SECTION>[^ \r\t\n].+[^ \r\t\n]  { yylval->emplace<std::string>(yytext, yyleng); return token::SYMBOL; }
<NAME_SECTION>{whitespace}+           {  }
<NAME_SECTION>[\n]                    { BEGIN(INITIAL); return static_cast<token_type>(*yytext); }

 /* gobble up white-spaces */
{whitespace}+ {
    yylloc->step();
}

 /* gobble up end-of-lines */
\n {
    mps_yycolumn=1;
    return static_cast<token_type>(*yytext);
}
 
 /* pass all other characters up to bison */
. {
    return static_cast<token_type>(*yytext);
}

%% /*** Additional Code ***/

namespace dlinear::mps {

MpsScanner::MpsScanner(std::istream* in, std::ostream* out) : MpsFlexLexer(in, out) {}

MpsScanner::~MpsScanner() {}

void MpsScanner::set_debug(const bool b) {
    yy_flex_debug = b;
}
}  // namespace dlinear::mps

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
