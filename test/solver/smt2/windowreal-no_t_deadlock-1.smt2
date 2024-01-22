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
(declare-fun x_1 () Bool)
(declare-fun x_2 () Bool)
(declare-fun x_3 () Bool)
(declare-fun x_4 () Bool)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Bool)
(declare-fun x_7 () Bool)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)
(declare-fun x_10 () Bool)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Bool)
(declare-fun x_13 () Bool)
(declare-fun x_14 () Real)
(declare-fun x_15 () Bool)
(declare-fun x_16 () Bool)
(declare-fun x_17 () Bool)
(declare-fun x_18 () Bool)
(declare-fun x_19 () Bool)
(declare-fun x_20 () Real)
(declare-fun x_21 () Real)
(declare-fun x_22 () Real)
(assert (let ((?v_5 (+ 0 x_8)) (?v_23 (= x_9 0)) (?v_4 (= x_10 x_3)) (?v_25 (and (= x_11 x_4) (= x_12 x_5))) (?v_12 (or x_0 x_1)) (?v_10 (not x_0))) (let ((?v_11 (and ?v_10 x_1)) (?v_29 (not x_4)) (?v_26 (not x_5))) (let ((?v_21 (and ?v_29 ?v_26)) (?v_24 (= x_13 x_7)) (?v_2 (= x_14 0)) (?v_7 (not x_1))) (let ((?v_0 (and ?v_10 ?v_7)) (?v_19 (or x_0 ?v_7)) (?v_1 (not x_15)) (?v_31 (or x_4 x_5)) (?v_36 (or ?v_29 x_5)) (?v_17 (or ?v_10 x_1)) (?v_35 (< 0 1)) (?v_8 (and x_0 ?v_7)) (?v_40 (or x_4 ?v_26)) (?v_27 (and x_4 ?v_26)) (?v_22 (= x_16 x_6)) (?v_3 (= x_17 x_2)) (?v_39 (< 0 6)) (?v_6 (and (= x_18 x_0) (= x_19 x_1))) (?v_30 (and ?v_29 x_5)) (?v_16 (< 0 2)) (?v_13 (<= ?v_5 1)) (?v_28 (= x_9 ?v_5)) (?v_9 (= x_14 ?v_5)) (?v_20 (<= ?v_5 3)) (?v_41 (<= ?v_5 6)) (?v_18 (<= ?v_5 2))) (let ((?v_32 (not ?v_13)) (?v_14 (= 0 2)) (?v_15 (or ?v_17 x_15)) (?v_33 (= 0 1)) (?v_37 (= 0 6)) (?v_34 (or ?v_36 x_15)) (?v_38 (or ?v_40 x_15))) (and (and (and (and (and (and (and (and (and (and (and (and (<= x_20 1) (>= x_20 0)) ?v_0) (not x_2)) (not x_3)) ?v_21) (not x_6)) (not x_7)) (not (< x_8 0))) (= x_20 (ite x_15 0 1))) (or (or (or (or (or (or (or (or (or (and (and (and (and (and (and (= x_21 0) ?v_0) ?v_1) ?v_6) ?v_3) ?v_2) ?v_4) (and (and (and (and (and (and (and (= x_21 1) ?v_0) ?v_1) x_18) (not x_19)) ?v_2) ?v_3) ?v_4)) (and (and (and (and (and (and (and (= x_21 2) ?v_0) x_15) ?v_13) ?v_9) ?v_3) ?v_6) ?v_4)) (and (and (and (and (and (and (and (and (= x_21 3) ?v_8) ?v_1) ?v_14) (not x_18)) x_19) ?v_2) ?v_3) ?v_4)) (and (and (and (and (and (and (and (= x_21 4) ?v_8) ?v_1) ?v_16) ?v_6) ?v_3) ?v_2) ?v_4)) (and (and (and (and (and (and (and (= x_21 5) ?v_8) x_15) ?v_18) ?v_9) ?v_3) ?v_6) ?v_4)) (and (and (and (and (and (and (and (= x_21 6) ?v_11) ?v_1) x_18) x_19) ?v_3) ?v_2) ?v_4)) (and (and (and (and (and (and (and (= x_21 7) ?v_11) x_15) ?v_20) ?v_9) ?v_3) ?v_6) ?v_4)) (and (and (and (and (and (and (= x_21 8) x_0) x_1) ?v_6) ?v_3) ?v_2) ?v_4)) (and (and (and (and (and (and (and (and (and (and (and (and (= x_21 9) (or ?v_12 x_15)) (or (or ?v_12 ?v_1) ?v_32)) (or ?v_15 (not ?v_14))) (or ?v_15 (not ?v_16))) (or (or ?v_17 ?v_1) (not ?v_18))) (or ?v_19 x_15)) (or (or ?v_19 ?v_1) (not ?v_20))) (or ?v_10 ?v_7)) ?v_2) ?v_3) ?v_6) ?v_4))) (or (or (or (or (or (or (or (or (or (or (and (and (and (and (and (and (and (= x_22 0) ?v_21) ?v_1) x_11) (not x_12)) ?v_23) ?v_22) ?v_24) (and (and (and (and (and (and (= x_22 1) ?v_21) ?v_1) ?v_25) ?v_22) ?v_23) ?v_24)) (and (and (and (and (and (and (and (= x_22 2) ?v_21) x_15) ?v_13) ?v_28) ?v_22) ?v_25) ?v_24)) (and (and (and (and (and (and (and (and (= x_22 3) ?v_27) ?v_1) ?v_33) (not x_11)) x_12) ?v_23) ?v_22) ?v_24)) (and (and (and (and (and (and (and (= x_22 4) ?v_27) ?v_1) ?v_35) ?v_25) ?v_22) ?v_23) ?v_24)) (and (and (and (and (and (and (and (= x_22 5) ?v_27) x_15) ?v_13) ?v_28) ?v_22) ?v_25) ?v_24)) (and (and (and (and (and (and (and (and (= x_22 6) ?v_30) ?v_1) ?v_37) x_11) x_12) ?v_23) ?v_22) ?v_24)) (and (and (and (and (and (and (and (= x_22 7) ?v_30) ?v_1) ?v_39) ?v_25) ?v_22) ?v_23) ?v_24)) (and (and (and (and (and (and (and (= x_22 8) ?v_30) x_15) ?v_41) ?v_28) ?v_22) ?v_25) ?v_24)) (and (and (and (and (and (and (= x_22 9) x_4) x_5) ?v_25) ?v_22) ?v_23) ?v_24)) (and (and (and (and (and (and (and (and (and (and (and (and (and (= x_22 10) (or ?v_31 x_15)) (or (or ?v_31 ?v_1) ?v_32)) (or ?v_34 (not ?v_33))) (or ?v_34 (not ?v_35))) (or (or ?v_36 ?v_1) ?v_32)) (or ?v_38 (not ?v_37))) (or ?v_38 (not ?v_39))) (or (or ?v_40 ?v_1) (not ?v_41))) (or ?v_29 ?v_26)) ?v_23) ?v_22) ?v_25) ?v_24))) (or x_17 x_2))))))))
(check-sat)
(exit)
