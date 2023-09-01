%{ /*** C++ Code ***/
#include "dlinear/smt2/logic.h"
%}

/*** yacc/bison Declarations ***/
%skeleton "lalr1.cc" /** C++ skeleton file */
%define api.parser.class {Smt2Parser} /** Parser class name */
/** Driver is a parameter passed to the parser */
%parse-param { class Smt2Driver& driver } 
%token TK_CHECK_SAT

%% /*** Grammar Rules ***/
command_check_sat: '('TK_CHECK_SAT ')' {
                    driver.CheckSat();
                }
                ;

%% /*** Additional Code ***/
void dlinear::Smt2Parser::error(const Smt2Parser::location_type& l, const std::string& m) {
    driver.error(l, m);
}
