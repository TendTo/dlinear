%{

#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

/* void yyerror(SmtPrsr parser, const char *); */
#define YYMAXDEPTH 1024 * 1024
%}

/*** yacc/bison Declarations ***/

/* Require bison 2.3 or later */
%require "3.2"

/* add debug output code to generated parser. disable this for release
 * versions. */
%debug

/* start symbol is named "script" */
%start script

/* write out a header file containing the token defines */
%defines

/* /\* use newer C++ skeleton file *\/ */
%skeleton "lalr1.cc"

/* namespace to enclose parser in */
%define api.prefix {dlinear}

/* set the parser's class identifier */
%define api.parser.class {MpsParser}

/* keep track of the current position within the input */
%locations
%initial-action
{
    // initialize the initial location object
    @$.begin.filename = @$.end.filename = &driver.mutable_streamname();
};

/* The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables. */
%parse-param { class MpsDriver& driver }

/* verbose error messages */
%define parse.error verbose


%union
{
    int64_t                   int64Val;
    std::string*              rationalVal;
    std::string*              stringVal;
    char                      charVal;
}

%token NEWLINE
%token NAME_DECLARATION ROWS_DECLARATION COLUMNS_DECLARATION RHS_DECLARATION RANGES_DECLARATION BOUNDS_DECLARATION ENDATA

%token                 END          0        "end of file"
%token <stringVal>     RATIONAL              "identifier"
%token <int64Val>      INT                   "int64"
%token <stringVal>     SYMBOL                "symbol"
%token <charVal>       SENSE                 "sense. Acceptable values are: E, L, G, N"
%token <stringVal>     BOUND_TYPE            "type of bound. Acceptable values are: LO, UP, FX, FR, MI, PL"

%type <stringVal> name

%{

#include "dlinear/mps/Driver.h"
#include "dlinear/mps/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.scanner_->lex

%}

%% /*** Grammar Rules ***/

script: name_section rows_section columns_section rhs_section ranges_declaration bounds_declaration ENDATA END
    ;

name_section: NAME_DECLARATION name { driver.mutable_streamname() = *$2; driver.print(*$2); }
    ;

name: /* empty */ { $$ = new std::string("unnamed"); }
    | SYMBOL { $$ = $1; }
    | name SYMBOL { $$ = new std::string(*$1); }
    ;

rows_section: ROWS_DECLARATION NEWLINE rows
    ;

rows: rows row
    |  row
    |
    ;

row: SENSE SYMBOL NEWLINE { driver.AddRow($1, *$2); }
    ;

columns_section: COLUMNS_DECLARATION NEWLINE columns
    ;

columns: columns column
    | column
    ;

    /* Field 1: Blank
        Field 2: Column identifier
        Field 3: Row identifier
        Field 4: Value of matrix coefficient specified by Fields 2 and 3
        Field 5: Row identifier (optional)
        Field 6: Value of matrix coefficient specified by Fields 2 and 5 (optional)
    */
column: SYMBOL SYMBOL RATIONAL SYMBOL RATIONAL NEWLINE { driver.AddColumn(*$2, *$1, std::stod(*$3)); driver.AddColumn(*$4, *$1, std::stod(*$5)); }
    | SYMBOL SYMBOL RATIONAL NEWLINE { driver.AddColumn(*$2, *$1, std::stod(*$3)); }
    ;

rhs_section: RHS_DECLARATION NEWLINE rhs
    ;

rhs: rhs rhs_row
    | rhs_row
    |
    ;

    /* Field 1: Blank
        Field 2: RHS identifier
        Field 3: Row identifier
        Field 4: Value of RHS coefficient specified by Field 2 and 3
        Field 5: Row identifier (optional)
        Field 6: Value of RHS coefficient specified by Field 2 and 5 (optional)
    */
rhs_row: SYMBOL SYMBOL RATIONAL SYMBOL RATIONAL NEWLINE { driver.AddRhs(*$2, *$1, std::stod(*$3)); driver.AddRhs(*$4, *$1, std::stod(*$5)); }
    | SYMBOL SYMBOL RATIONAL NEWLINE { driver.AddRhs(*$2, *$1, std::stod(*$3)); }
    ;

ranges_declaration: /* empty */
    | RANGES_DECLARATION NEWLINE ranges
    ;

ranges: ranges range
    | range
    ;

    /* Field 1: Blank
        Field 2: Righthand side range vector identifier
        Field 3: Row identifier
        Field 4: Value of the range applied to row specified by Field 3
        Field 5: Row identifier (optional)
        Field 6: Value of the range applied to row specified by Field 5 (optional)
    */
range: SYMBOL SYMBOL RATIONAL SYMBOL RATIONAL NEWLINE { driver.AddRange(*$2, *$1, std::stod(*$3)); driver.AddRange(*$4, *$1, std::stod(*$5)); }
    | SYMBOL SYMBOL RATIONAL NEWLINE { driver.AddRange(*$2, *$1, std::stod(*$3)); }
    ;

bounds_declaration: /* empty */
    | BOUNDS_DECLARATION NEWLINE bounds
    ;

bounds: bounds bound
    | bound
    ;

    /* Field 1: Type of bound. Acceptable values are:
        - LO Lower bound
        - UP Upper bound
        - FX Fixed value (upper and lower bound the same)
        - FR Free variable (lower bound -∞ and upper bound +∞)
        - MI Minus infinity (lower bound = -∞)
        - PL Plus infinity (upper bound = +∞)
        Field 2: Bound identifier
        Field 3: Column identifier to be bounded
        Field 4: Value of the specified bound
        Fields 5 and 6 are not used in the BOUNDS section.
    */
bound: BOUND_TYPE SYMBOL SYMBOL RATIONAL NEWLINE { driver.AddBound(*$2, *$3, std::stod(*$4), *$1); }

%% /*** Additional Code ***/

void dlinear::MpsParser::error(const MpsParser::location_type& l, const std::string& m) {
    driver.error(l, m);
}

#pragma GCC diagnostic pop
