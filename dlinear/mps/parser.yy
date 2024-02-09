%{

#include <cmath>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <tuple>
#include <utility>

#include "dlinear/libs/gmp.h"
#include "dlinear/mps/Sense.h"
#include "dlinear/mps/BoundType.h"

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


%union
{
    std::string* stringVal;
    Sense        senseVal;
    BoundType    boundTypeVal;
}

%token NAME_DECLARATION ROWS_DECLARATION COLUMNS_DECLARATION RHS_DECLARATION RANGES_DECLARATION BOUNDS_DECLARATION OBJSENSE_DECLARATION OBJNAME_DECLARATION ENDATA
%token MIN MAX

%token                 END          0        "end of file"
%token <stringVal>     SYMBOL                "symbol"
%token <stringVal>     QUOTED_SYMBOL         "symbol in quotes"
%token <senseVal>      SENSE                 "sense. Acceptable values are: E, L, G, N"
%token <boundTypeVal>  BOUND_TYPE            "type of bound. Acceptable values are: LO, UP, FX"
%token <boundTypeVal>  BOUND_TYPE_SINGLE     "type of bound. Can only be BV, MI, PL, FR"

%destructor { delete $$; } SYMBOL

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
    | objsense_section
    | objname_section
    | columns_section
    | rhs_section
    | ranges_section
    | bounds_section
    | end_section
    ;

name_section: NAME_DECLARATION SYMBOL '\n' { 
        driver.m_problem_name() = *$2;
        delete $2;
    }
    | NAME_DECLARATION '\n' { driver.m_problem_name() = "unnamed"; }
    ;

objsense_section: OBJSENSE_DECLARATION '\n' MAX '\n' { driver.ObjectiveSense(false); }
    | OBJSENSE_DECLARATION '\n' MIN '\n' { driver.ObjectiveSense(true); }
    ;

objname_section: OBJNAME_DECLARATION '\n' SYMBOL '\n' { driver.ObjectiveName(*$3); delete $3; }
    ;

rows_section: ROWS_DECLARATION '\n'
    | ROWS_DECLARATION '\n' rows
    ;

rows: rows row
    |  row
    ;

row: SENSE SYMBOL '\n' { driver.AddRow($1, *$2); delete $2; }
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
        driver.AddColumn(*$1, *$2, mpq_class{string_to_mpq(*$3)}); 
        driver.AddColumn(*$1, *$4, mpq_class{string_to_mpq(*$5)});
        delete $1;
        delete $2;
        delete $3;
        delete $4;
        delete $5;
    }
    | SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddColumn(*$1, *$2, mpq_class{string_to_mpq(*$3)}); 
        delete $1;
        delete $2;
        delete $3;
    }
    | SYMBOL QUOTED_SYMBOL QUOTED_SYMBOL '\n' { delete $1; delete $2; delete $3;}
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
        driver.AddRhs(*$1, *$2, mpq_class{string_to_mpq(*$3)});
        driver.AddRhs(*$1, *$4, mpq_class{string_to_mpq(*$5)});
        delete $1;
        delete $2;
        delete $3;
        delete $4;
        delete $5;
    }
    | SYMBOL SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRhs("", *$1, mpq_class{string_to_mpq(*$2)});
        driver.AddRhs("", *$3, mpq_class{string_to_mpq(*$4)});
        delete $1;
        delete $2;
        delete $3;
        delete $4;
    }
    | SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRhs(*$1, *$2, mpq_class{string_to_mpq(*$3)});
        delete $1;
        delete $2;
        delete $3;
    }
    | SYMBOL SYMBOL '\n' { 
        driver.AddRhs("", *$1, mpq_class{string_to_mpq(*$2)});
        delete $1;
        delete $2;
    }
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
        driver.AddRange(*$1, *$2, mpq_class{string_to_mpq(*$3)});
        driver.AddRange(*$1, *$4, mpq_class{string_to_mpq(*$5)});
        delete $1;
        delete $2;
        delete $3;
        delete $4;
        delete $5;
    }
    | SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddRange(*$1, *$2, mpq_class{string_to_mpq(*$3)}); 
        delete $1;
        delete $2;
        delete $3;
    }
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
        driver.AddBound($1, *$2, *$3, mpq_class{string_to_mpq(*$4)});
        delete $2;
        delete $3;
        delete $4;
    }
    | BOUND_TYPE SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, "", *$2, mpq_class{string_to_mpq(*$3)});
        delete $2;
        delete $3;
    }
    | BOUND_TYPE_SINGLE SYMBOL SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, *$2, *$3);
        delete $2;
        delete $3;
        delete $4;
    }
    | BOUND_TYPE_SINGLE SYMBOL SYMBOL '\n' { 
        driver.AddBound($1, *$2, *$3);
        delete $2;
        delete $3;
    }
    | '\n'

end_section: ENDATA '\n'
    | ENDATA { driver.End(); }
    ;

%% /*** Additional Code ***/

void dlinear::mps::MpsParser::error(const MpsParser::location_type& l, const std::string& m) {
    driver.error(l, m);
}

#pragma GCC diagnostic pop
