(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
SAL benchmark suite.  Created at SRI by Bruno Dutertre, John Rushby, Maria
Sorea, and Leonardo de Moura.  Contact demoura@csl.sri.com for more
information.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun x_0 () Bool)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Bool)
(assert (let ((?v_0 (not x_0)) (?v_2 (= x_1 0)) (?v_5 (+ 0 x_2)) (?v_4 (= x_3 0)) (?v_3 (= x_4 0)) (?v_1 (not x_5))) (and (and (and (and (and (and (<= x_7 1) (>= x_7 0)) ?v_0) (not (< x_6 0))) (= x_7 (ite x_5 0 1))) (or (or (and (and (and (and (and (and (= x_8 0) ?v_1) ?v_0) x_9) ?v_2) ?v_3) ?v_4) (and (and (and (and (and (and (and (= x_8 1) ?v_1) x_0) (not (< 0 30))) (not x_9)) ?v_2) ?v_3) ?v_4)) (and (and (and (and (and (and (and (= x_8 2) x_5) (not (< x_2 0))) (or x_0 (<= ?v_5 1))) (= x_1 ?v_5)) (= x_4 ?v_5)) (= x_3 (ite ?v_0 ?v_5 0))) (= x_9 x_0)))) (or (and (not (< x_4 60)) (not (<= (* x_3 20) x_4))) (and (not (< 0 60)) (not (<= (* 0 20) 0)))))))
(check-sat)
(exit)
