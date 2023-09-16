%{

#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

#include "dlinear/mps/Sense.h"
#include "dlinear/mps/BoundType.h"

/* void yyerror(SmtPrsr parser, const char *); */
#define YYMAXDEPTH 1024 * 1024
%}

/*** yacc/bison Declarations ***/

/* Require bison 2.3 or later */
%require "3.2"

/* add debug output code to generated parser. disable this for release
 * versions. */
%define parse.trace

/* start symbol is named "script" */
%start script

/* write out a header file containing the token defines */
%defines

/* use newer C++ skeleton file */
%skeleton "lalr1.cc"

/* namespace to enclose parser in */
%define api.namespace {dlinear::mps}

/* set the parser's class identifier */
%define api.parser.class {MpsParser}

/* keep track of the current position within the input */
%locations
%initial-action
{
    // initialize the initial location object
    @$.begin.filename = @$.end.filename = &driver.mutable_stream_name();
};

/* The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables. */
%parse-param { class MpsDriver& driver }

/* verbose error messages */
%define parse.error verbose


%union
{
    std::string*              rationalVal;
    std::string*              stringVal;
    Sense       senseVal;
    BoundType   boundTypeVal;
}

%token '\n'
%token NAME_DECLARATION ROWS_DECLARATION COLUMNS_DECLARATION RHS_DECLARATION RANGES_DECLARATION BOUNDS_DECLARATION ENDATA

%token                 END          0        "end of file"
%token <stringVal>     RATIONAL              "rational number"
%token <stringVal>     SYMBOL                "symbol"
%token <senseVal>      SENSE                 "sense. Acceptable values are: E, L, G, N"
%token <boundTypeVal>  BOUND_TYPE            "type of bound. Acceptable values are: LO, UP, FX, FR, MI, PL"

%type <stringVal> name

%destructor { delete $$; } RATIONAL SYMBOL

%{

#include "dlinear/mps/Driver.h"
#include "dlinear/mps/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.scanner()->lex

%}

%% /*** Grammar Rules ***/

script: sections END
    ;

sections: sections section
    | section
    ;

section: name_section
    | rows_section
    | columns_section
    | rhs_section
    | ranges_section
    | bounds_section
    | end_section
    ;

name_section: NAME_DECLARATION name '\n' { 
        driver.mutable_problem_name() = *$2;
        delete $2;
    }
    | NAME_DECLARATION '\n' { driver.mutable_problem_name() = "unnamed"; }
    ;

name: SYMBOL { $$ = $1; }
    | name SYMBOL { $$ = new std::string(*$1); delete $2; }
    ;

rows_section: ROWS_DECLARATION '\n'
    | ROWS_DECLARATION '\n' rows
    ;

rows: rows row
    |  row
    ;

row: SENSE SYMBOL '\n' { driver.AddRow($1, *$2); }
    ;

columns_section: COLUMNS_DECLARATION '\n' columns
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
column: SYMBOL SYMBOL RATIONAL SYMBOL RATIONAL '\n' { 
        driver.AddColumn(*$2, *$1, std::stod(*$3)); 
        driver.AddColumn(*$4, *$1, std::stod(*$5));
        delete $1;
        delete $2;
        delete $3;
        delete $4;
        delete $5;
    }
    | SYMBOL SYMBOL RATIONAL '\n' { 
        driver.AddColumn(*$2, *$1, std::stod(*$3)); 
        delete $1;
        delete $2;
        delete $3;
    }
    ;

rhs_section: RHS_DECLARATION '\n' rhs
    ;

rhs: rhs rhs_row
    | rhs_row
    ;

    /* Field 1: Blank
        Field 2: RHS identifier
        Field 3: Row identifier
        Field 4: Value of RHS coefficient specified by Field 2 and 3
        Field 5: Row identifier (optional)
        Field 6: Value of RHS coefficient specified by Field 2 and 5 (optional)
    */
rhs_row: SYMBOL SYMBOL RATIONAL SYMBOL RATIONAL '\n' { 
        driver.AddRhs(*$2, *$1, std::stod(*$3));
        driver.AddRhs(*$4, *$1, std::stod(*$5));
        delete $1;
        delete $2;
        delete $3;
        delete $4;
        delete $5;
    }
    | SYMBOL SYMBOL RATIONAL '\n' { 
        driver.AddRhs(*$2, *$1, std::stod(*$3));
        delete $1;
        delete $2;
        delete $3;
    }
    ;

ranges_section: RANGES_DECLARATION '\n' ranges
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
range: SYMBOL SYMBOL RATIONAL SYMBOL RATIONAL '\n' { 
        driver.AddRange(*$2, *$1, std::stod(*$3));
        driver.AddRange(*$4, *$1, std::stod(*$5));
        delete $1;
        delete $2;
        delete $3;
        delete $4;
        delete $5;
    }
    | SYMBOL SYMBOL RATIONAL '\n' { 
        driver.AddRange(*$2, *$1, std::stod(*$3)); 
        delete $1;
        delete $2;
        delete $3;
    }
    ;

bounds_section: BOUNDS_DECLARATION '\n' bounds
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
bound: BOUND_TYPE SYMBOL SYMBOL RATIONAL '\n' { 
        driver.AddBound(*$3, *$2, std::stod(*$4), $1);
        delete $2;
        delete $3;
        delete $4;
    }

end_section: ENDATA '\n'
    | ENDATA { driver.End(); }
    ;

%% /*** Additional Code ***/

void dlinear::mps::MpsParser::error(const MpsParser::location_type& l, const std::string& m) {
    driver.error(l, m);
}

#pragma GCC diagnostic pop
