%{

#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

#include "dlinear/libs/libgmp.h"
#include "dlinear/parser/mps/Sense.h"
#include "dlinear/parser/mps/BoundType.h"
#include "dlinear/util/exception.h"

using dlinear::gmp::string_to_mpq;

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
    @$.begin.filename = @$.end.filename = &driver.m_stream_name();
};

/* The driver is passed by reference to the parser and to the scanner. This
 * provides a simple but effective pure interface, not relying on global
 * variables. */
%parse-param { class MpsDriver& driver }

/* verbose error messages */
%define parse.error verbose

/* use the built-in variant type for semantic values instead of the old %union */
%define api.value.type variant

%token NAME_DECLARATION ROWS_DECLARATION COLUMNS_DECLARATION RHS_DECLARATION RANGES_DECLARATION BOUNDS_DECLARATION OBJSENSE_DECLARATION OBJNAME_DECLARATION ENDATA
%token MIN MAX
%token SET_INFO SET_OPTION

%token                 END          0        "end of file"
%token <std::string>   RATIONAL              "rational used in comments"
%token <std::string>   SYMBOL                "symbol"
%token <std::string>   QUOTED_SYMBOL         "symbol in quotes"
%token <Sense>         SENSE                 "sense. Acceptable values are: E, L, G, N"
%token <BoundType>     BOUND_TYPE            "type of bound. Acceptable values are: LO, UP, FX"
%token <BoundType>     BOUND_TYPE_SINGLE     "type of bound. Can only be BV, MI, PL, FR"

%type <std::string> generic_string

%{

#include "dlinear/parser/mps/Driver.h"
#include "dlinear/parser/mps/scanner.h"

/* this "connects" the bison parser in the driver to the flex scanner class
 * object. it defines the yylex() function call to pull the next token from the
 * current lexer object of the driver context. */
#undef yylex
#define yylex driver.scanner()->lex

%}

%% /*** Grammar Rules ***/

generic_string: SYMBOL
        | QUOTED_SYMBOL
        | RATIONAL
        ;

script: sections END
    ;

sections: sections section
    | section
    | commands
    ;

commands: commands command
    | command
    ;

section: name_section
    | rows_section
    | objsense_section
    | objname_section
    | columns_section
    | rhs_section
    | ranges_section
    | bounds_section
    | end_section
    ;

name_section: NAME_DECLARATION SYMBOL '\n' { 
        driver.m_problem_name() = $2;
    }
    | NAME_DECLARATION '\n' { driver.m_problem_name() = "unnamed"; }
    ;

objsense_section: OBJSENSE_DECLARATION '\n' MAX '\n' { driver.ObjectiveSense(false); }
    | OBJSENSE_DECLARATION '\n' MIN '\n' { driver.ObjectiveSense(true); }
    ;

objname_section: OBJNAME_DECLARATION '\n' SYMBOL '\n' { driver.ObjectiveName($3); }
    ;

rows_section: ROWS_DECLARATION '\n'
    | ROWS_DECLARATION '\n' rows
    ;

rows: rows row
    |  row
    ;

row: SENSE SYMBOL '\n' { driver.AddRow($1, $2); }
    | command
    | '\n'
    ;

columns_section: COLUMNS_DECLARATION '\n'
    | COLUMNS_DECLARATION '\n' columns
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
column: SYMBOL SYMBOL SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddColumn($1, $2, mpq_class{string_to_mpq($3)}); 
        driver.AddColumn($1, $4, mpq_class{string_to_mpq($5)});
    }
    | SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddColumn($1, $2, mpq_class{string_to_mpq($3)}); 
    }
    | SYMBOL QUOTED_SYMBOL QUOTED_SYMBOL '\n' { }
    | command
    | '\n'
    ;

rhs_section: RHS_DECLARATION '\n'
    | RHS_DECLARATION '\n' rhs
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
rhs_row: SYMBOL SYMBOL SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRhs($1, $2, mpq_class{string_to_mpq($3)});
        driver.AddRhs($1, $4, mpq_class{string_to_mpq($5)});
    }
    | SYMBOL SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRhs("", $1, mpq_class{string_to_mpq($2)});
        driver.AddRhs("", $3, mpq_class{string_to_mpq($4)});
    }
    | SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRhs($1, $2, mpq_class{string_to_mpq($3)});
    }
    | SYMBOL SYMBOL '\n' { 
        driver.AddRhs("", $1, mpq_class{string_to_mpq($2)});
    }
    | command
    | '\n'
    ;

ranges_section: RANGES_DECLARATION '\n'
    | RANGES_DECLARATION '\n' ranges
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
range: SYMBOL SYMBOL SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRange($1, $2, mpq_class{string_to_mpq($3)});
        driver.AddRange($1, $4, mpq_class{string_to_mpq($5)});
    }
    | SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRange($1, $2, mpq_class{string_to_mpq($3)}); 
    }
    | command
    | '\n'
    ;

bounds_section: BOUNDS_DECLARATION '\n'
    | BOUNDS_DECLARATION '\n' bounds
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
bound: BOUND_TYPE SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, $2, $3, mpq_class{string_to_mpq($4)});
    }
    | BOUND_TYPE SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, "", $2, mpq_class{string_to_mpq($3)});
    }
    | BOUND_TYPE_SINGLE SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, $2, $3);
    }
    | BOUND_TYPE_SINGLE SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, $2, $3);
    }
    | command
    | '\n'
    ;

end_section: ENDATA {
        driver.End(); 
        YYACCEPT;
    }
    ;

/**
 * Extension to the standarm MPS format to support smt2 like commands
 * to set info (e.g. expected result) and options for the LP solver
 */
command: SET_INFO SYMBOL generic_string '\n' {
        driver.SetInfo($2, $3);
    }
    | SET_OPTION SYMBOL generic_string '\n'{
        driver.SetOption($2, $3);
    }
    ;


%% /*** Additional Code ***/

void dlinear::mps::MpsParser::error(const MpsParser::location_type& l, const std::string& m) {
    driver.error(l, m);
}

#pragma GCC diagnostic pop
