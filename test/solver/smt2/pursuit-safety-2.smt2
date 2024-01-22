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
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Bool)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Bool)
(declare-fun x_9 () Real)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Real)
(declare-fun x_13 () Real)
(declare-fun x_14 () Bool)
(declare-fun x_15 () Bool)
(declare-fun x_16 () Real)
(declare-fun x_17 () Real)
(declare-fun x_18 () Real)
(declare-fun x_19 () Real)
(declare-fun x_20 () Real)
(declare-fun x_21 () Real)
(assert (let ((?v_3 (= x_6 40)) (?v_28 (+ x_6 (* x_9 6))) (?v_4 (= x_6 0)) (?v_2 (= x_3 40)) (?v_6 (= x_3 0)) (?v_13 (< (+ (- (* x_6 5) (* x_3 6)) 40) 0)) (?v_31 (+ x_3 (* x_9 5))) (?v_29 (+ x_7 x_9)) (?v_10 (= x_7 2)) (?v_7 (= x_13 x_3)) (?v_24 (not x_4))) (let ((?v_30 (and ?v_24 x_5)) (?v_15 (not x_5))) (let ((?v_18 (and x_4 ?v_15)) (?v_5 (and (= x_14 x_4) (= x_15 x_5))) (?v_8 (= x_16 x_6)) (?v_1 (and ?v_24 ?v_15)) (?v_14 (= x_17 0)) (?v_21 (not x_14))) (let ((?v_17 (and ?v_21 x_15)) (?v_0 (= x_10 0)) (?v_12 (not ?v_2)) (?v_9 (= x_17 x_7)) (?v_27 (or ?v_24 x_5)) (?v_11 (not ?v_6)) (?v_26 (or x_4 x_5)) (?v_20 (not ?v_13)) (?v_16 (or ?v_6 ?v_2)) (?v_19 (= x_16 (ite ?v_3 0 (ite ?v_4 40 x_6)))) (?v_25 (and (and (<= ?v_29 2) (not (< ?v_31 0))) (<= ?v_28 40))) (?v_36 (= 10 40)) (?v_56 (+ 10 (* x_2 6))) (?v_37 (= 10 0)) (?v_35 (= 20 40)) (?v_39 (= 20 0)) (?v_45 (< (+ (- (* 10 5) (* 20 6)) 40) 0)) (?v_59 (+ 20 (* x_2 5))) (?v_57 (+ 2 x_2)) (?v_42 (= 2 2)) (?v_40 (= x_3 20)) (?v_52 (not x_0))) (let ((?v_58 (and ?v_52 x_1)) (?v_47 (not x_1))) (let ((?v_49 (and x_0 ?v_47)) (?v_38 (and (= x_4 x_0) (= x_5 x_1))) (?v_41 (= x_6 10)) (?v_33 (and ?v_52 ?v_47)) (?v_46 (= x_7 0)) (?v_34 (not x_8)) (?v_44 (not ?v_35)) (?v_55 (or ?v_52 x_1)) (?v_43 (not ?v_39)) (?v_54 (or x_0 x_1)) (?v_51 (not ?v_45)) (?v_48 (or ?v_39 ?v_35)) (?v_50 (= x_6 (ite ?v_36 0 (ite ?v_37 40 10)))) (?v_53 (and (and (<= ?v_57 2) (not (< ?v_59 0))) (<= ?v_56 40))) (?v_23 (= x_10 1)) (?v_22 (not x_15)) (?v_32 (not (< x_9 0)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_19 1) (>= x_19 0)) (<= x_10 1)) (>= x_10 0)) ?v_33) (not (< x_18 0))) (= x_19 (ite ?v_23 0 1))) (not (< x_20 0))) (or (or (or (or (or (or (or (or (and (and (and (and (and (and (and (and (and (and (= x_21 0) ?v_0) ?v_1) ?v_10) ?v_11) ?v_12) ?v_13) ?v_14) ?v_7) ?v_8) ?v_5) (and (and (and (and (and (and (and (= x_21 1) ?v_0) ?v_1) (or (or ?v_2 ?v_4) ?v_3)) (= x_13 (ite ?v_2 0 x_3))) ?v_19) ?v_5) ?v_9)) (and (and (and (and (and (and (and (= x_21 2) ?v_0) ?v_1) ?v_16) ?v_17) ?v_7) ?v_8) ?v_9)) (and (and (and (and (and (and (and (and (and (and (and (= x_21 3) ?v_0) ?v_1) ?v_10) ?v_11) ?v_12) ?v_20) x_14) ?v_22) ?v_14) ?v_7) ?v_8)) (and (and (and (and (and (and (and (= x_21 4) ?v_0) ?v_18) ?v_16) ?v_17) ?v_7) ?v_8) ?v_9)) (and (and (and (and (and (and (and (= x_21 5) ?v_0) ?v_18) (or (or ?v_6 ?v_4) ?v_3)) (= x_13 (ite ?v_6 40 x_3))) ?v_19) ?v_5) ?v_9)) (and (and (and (and (and (and (and (and (and (and (= x_21 6) ?v_0) ?v_18) ?v_10) ?v_11) ?v_12) ?v_20) ?v_14) ?v_7) ?v_8) ?v_5)) (and (and (and (and (and (and (and (and (and (and (and (= x_21 7) ?v_0) ?v_18) ?v_10) ?v_11) ?v_12) ?v_13) ?v_21) ?v_22) ?v_14) ?v_7) ?v_8)) (and (and (and (and (and (and (and (and (and (= x_21 8) ?v_23) ?v_32) (or ?v_26 ?v_25)) (or ?v_27 ?v_25)) (or (and ?v_26 ?v_27) (and (not (< (* x_20 2) (- (* x_6 2) x_9))) (<= x_20 ?v_28)))) (= x_17 (ite ?v_30 x_7 ?v_29))) (= x_13 (ite ?v_30 x_3 ?v_31))) (= x_16 (ite ?v_30 x_6 x_20))) ?v_5))) ?v_32) (= x_10 (ite x_8 0 1))) (not (< x_11 0))) (or (or (or (or (or (or (or (or (and (and (and (and (and (and (and (and (and (and (= x_12 0) ?v_34) ?v_33) ?v_42) ?v_43) ?v_44) ?v_45) ?v_46) ?v_40) ?v_41) ?v_38) (and (and (and (and (and (and (and (= x_12 1) ?v_34) ?v_33) (or (or ?v_35 ?v_37) ?v_36)) (= x_3 (ite ?v_35 0 20))) ?v_50) ?v_38) ?v_10)) (and (and (and (and (and (and (and (= x_12 2) ?v_34) ?v_33) ?v_48) ?v_30) ?v_40) ?v_41) ?v_10)) (and (and (and (and (and (and (and (and (and (and (and (= x_12 3) ?v_34) ?v_33) ?v_42) ?v_43) ?v_44) ?v_51) x_4) ?v_15) ?v_46) ?v_40) ?v_41)) (and (and (and (and (and (and (and (= x_12 4) ?v_34) ?v_49) ?v_48) ?v_30) ?v_40) ?v_41) ?v_10)) (and (and (and (and (and (and (and (= x_12 5) ?v_34) ?v_49) (or (or ?v_39 ?v_37) ?v_36)) (= x_3 (ite ?v_39 40 20))) ?v_50) ?v_38) ?v_10)) (and (and (and (and (and (and (and (and (and (and (= x_12 6) ?v_34) ?v_49) ?v_42) ?v_43) ?v_44) ?v_51) ?v_46) ?v_40) ?v_41) ?v_38)) (and (and (and (and (and (and (and (and (and (and (and (= x_12 7) ?v_34) ?v_49) ?v_42) ?v_43) ?v_44) ?v_45) ?v_24) ?v_15) ?v_46) ?v_40) ?v_41)) (and (and (and (and (and (and (and (and (and (= x_12 8) x_8) (not (< x_2 0))) (or ?v_54 ?v_53)) (or ?v_55 ?v_53)) (or (and ?v_54 ?v_55) (and (not (< (* x_11 2) (- (* 10 2) x_2))) (<= x_11 ?v_56)))) (= x_7 (ite ?v_58 2 ?v_57))) (= x_3 (ite ?v_58 20 ?v_59))) (= x_6 (ite ?v_58 10 x_11))) ?v_38))) (or (or (= x_13 x_16) (= x_3 x_6)) (= 20 10))) (or ?v_47 ?v_52)) (or ?v_15 ?v_24)) (or ?v_22 ?v_21)))))))))
(check-sat)
(exit)
