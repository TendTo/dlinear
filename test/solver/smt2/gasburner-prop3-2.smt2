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
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Real)
(declare-fun x_13 () Real)
(declare-fun x_14 () Real)
(declare-fun x_15 () Real)
(declare-fun x_16 () Bool)
(assert (let ((?v_6 (not x_9)) (?v_1 (= x_10 0)) (?v_5 (+ x_1 x_6)) (?v_3 (= x_11 x_3)) (?v_2 (= x_12 x_4)) (?v_0 (= x_7 0)) (?v_8 (not x_0)) (?v_10 (= x_1 0)) (?v_13 (+ 0 x_2)) (?v_12 (= x_3 0)) (?v_11 (= x_4 0)) (?v_9 (not x_5)) (?v_4 (= x_7 1)) (?v_7 (not (< x_6 0)))) (and (and (and (and (and (and (and (and (and (and (and (<= x_14 1) (>= x_14 0)) (<= x_7 1)) (>= x_7 0)) ?v_8) (not (< x_13 0))) (= x_14 (ite ?v_4 0 1))) (or (or (and (and (and (and (and (and (= x_15 0) ?v_0) ?v_6) x_16) ?v_1) ?v_2) ?v_3) (and (and (and (and (and (and (and (= x_15 1) ?v_0) x_9) (not (< x_1 30))) (not x_16)) ?v_1) ?v_2) ?v_3)) (and (and (and (and (and (and (and (= x_15 2) ?v_4) ?v_7) (or x_9 (<= ?v_5 1))) (= x_10 ?v_5)) (= x_12 (+ x_4 x_6))) (= x_11 (ite ?v_6 (+ x_3 x_6) x_3))) (= x_16 x_9)))) ?v_7) (= x_7 (ite x_5 0 1))) (or (or (and (and (and (and (and (and (= x_8 0) ?v_9) ?v_8) x_9) ?v_10) ?v_11) ?v_12) (and (and (and (and (and (and (and (= x_8 1) ?v_9) x_0) (not (< 0 30))) ?v_6) ?v_10) ?v_11) ?v_12)) (and (and (and (and (and (and (and (= x_8 2) x_5) (not (< x_2 0))) (or x_0 (<= ?v_13 1))) (= x_1 ?v_13)) (= x_4 ?v_13)) (= x_3 (ite ?v_8 ?v_13 0))) (= x_9 x_0)))) (or (or (and (not (< x_12 60)) (not (<= (* x_11 20) x_12))) (and (not (< x_4 60)) (not (<= (* x_3 20) x_4)))) (and (not (< 0 60)) (not (<= (* 0 20) 0)))))))
(check-sat)
(exit)
