(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
The Formal Verification of a Reintegration Protocol. Author: Lee Pike. Website: http://www.cs.indiana.edu/~lepike/pub_pages/emsoft.html.

This benchmark was automatically translated into SMT-LIB format from
CVC format using CVC Lite
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun x_0 () Real)
(declare-fun x_1 () Bool)
(declare-fun x_2 () Real)
(declare-fun x_3 () Bool)
(declare-fun x_4 () Real)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)
(declare-fun x_10 () Bool)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Real)
(declare-fun x_13 () Real)
(declare-fun x_14 () Bool)
(declare-fun x_15 () Bool)
(declare-fun x_16 () Bool)
(declare-fun x_17 () Bool)
(declare-fun x_18 () Bool)
(declare-fun x_19 () Bool)
(declare-fun x_20 () Bool)
(declare-fun x_21 () Bool)
(declare-fun x_22 () Bool)
(declare-fun x_23 () Bool)
(declare-fun x_24 () Real)
(declare-fun x_25 () Real)
(declare-fun x_26 () Real)
(declare-fun x_27 () Real)
(declare-fun x_28 () Real)
(declare-fun x_29 () Bool)
(declare-fun x_30 () Bool)
(declare-fun x_31 () Bool)
(declare-fun x_32 () Bool)
(declare-fun x_33 () Bool)
(declare-fun x_34 () Bool)
(declare-fun x_35 () Bool)
(declare-fun x_36 () Bool)
(declare-fun x_37 () Bool)
(declare-fun x_38 () Real)
(declare-fun x_39 () Real)
(declare-fun x_40 () Real)
(declare-fun x_41 () Real)
(declare-fun x_42 () Real)
(declare-fun x_43 () Real)
(declare-fun x_44 () Real)
(declare-fun x_45 () Real)
(declare-fun x_46 () Real)
(declare-fun x_47 () Real)
(declare-fun x_48 () Real)
(declare-fun x_49 () Real)
(declare-fun x_50 () Real)
(declare-fun x_51 () Real)
(declare-fun x_52 () Real)
(declare-fun x_53 () Bool)
(declare-fun x_54 () Real)
(declare-fun x_55 () Real)
(declare-fun x_56 () Real)
(assert (let ((?v_27 (+ x_6 x_7)) (?v_69 (<= x_8 x_9)) (?v_52 (= x_10 x_11)) (?v_13 (= x_12 0)) (?v_14 (< x_8 x_13)) (?v_36 (= x_9 x_8)) (?v_59 (= x_12 2)) (?v_61 (= x_14 x_15)) (?v_62 (and (= x_16 x_3) (= x_17 x_5))) (?v_50 (= x_18 x_19)) (?v_51 (and (= x_20 x_21) (= x_22 x_23))) (?v_63 (= x_24 x_25)) (?v_64 (and (= x_26 x_2) (= x_27 x_4))) (?v_24 (= x_28 x_13)) (?v_49 (= x_29 x_1)) (?v_47 (= x_30 x_31)) (?v_48 (and (= x_32 x_33) (= x_34 x_35))) (?v_65 (= x_36 x_37)) (?v_70 (- x_38 x_6)) (?v_40 (= x_12 1)) (?v_44 (+ x_7 x_6)) (?v_39 (<= x_39 x_9))) (let ((?v_46 (= x_14 (or x_15 (and ?v_39 x_31)))) (?v_29 (<= x_42 ?v_27)) (?v_31 (<= x_43 ?v_27)) (?v_28 (<= x_42 x_7)) (?v_30 (<= x_43 x_7)) (?v_8 (not x_3)) (?v_53 (< x_42 x_8)) (?v_54 (= x_9 x_42)) (?v_9 (not x_5)) (?v_55 (< x_43 x_8)) (?v_56 (= x_9 x_43)) (?v_17 (not x_15)) (?v_71 (not ?v_69)) (?v_33 (not x_33)) (?v_34 (not x_35)) (?v_35 (not x_31))) (let ((?v_25 (not ?v_28))) (let ((?v_37 (and ?v_25 (<= x_42 x_9))) (?v_26 (not ?v_30))) (let ((?v_38 (and ?v_26 (<= x_43 x_9)))) (let ((?v_45 (and (= x_16 (or x_3 (and ?v_37 x_33))) (= x_17 (or x_5 (and ?v_38 x_35))))) (?v_32 (<= x_39 ?v_27)) (?v_57 (< x_39 x_8)) (?v_58 (= x_9 x_39)) (?v_41 (not ?v_29)) (?v_42 (not ?v_31)) (?v_3 (and (not (<= x_39 x_7)) ?v_39)) (?v_4 (and (not (<= x_44 x_7)) (<= x_44 x_9)))) (let ((?v_43 (not ?v_32)) (?v_0 (= x_2 0)) (?v_1 (= x_4 0)) (?v_23 (= x_24 0)) (?v_12 (= x_24 3)) (?v_19 (= x_26 0)) (?v_10 (= x_26 3)) (?v_21 (= x_27 0)) (?v_11 (= x_27 3)) (?v_66 (= x_0 0))) (let ((?v_67 (not ?v_66)) (?v_5 (and (not (<= x_47 x_7)) (<= x_47 x_9))) (?v_15 (= x_26 (ite ?v_8 (ite (and ?v_37 (< x_2 3)) (+ x_2 1) x_2) x_2))) (?v_16 (= x_27 (ite ?v_9 (ite (and ?v_38 (< x_4 3)) (+ x_4 1) x_4) x_4))) (?v_18 (or x_3 ?v_10)) (?v_20 (or x_5 ?v_11)) (?v_22 (or x_15 ?v_12)) (?v_68 (= x_0 1)) (?v_2 (ite ?v_3 2 1)) (?v_6 (ite ?v_3 3 2)) (?v_7 (ite ?v_3 1 0)) (?v_60 (<= (ite x_19 (ite x_23 (ite x_21 3 2) x_40) (ite x_23 x_40 (ite x_21 1 0))) (* (* (ite x_15 (ite x_5 (ite x_3 0 1) x_41) (ite x_5 x_41 (ite x_3 2 3))) 1) (/ 1 2))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_12 2) (>= x_12 0)) (<= x_0 2)) (>= x_0 0)) (or (or (or ?v_0 (= x_2 1)) (= x_2 2)) (= x_2 3))) (not (< x_2 0))) (<= x_2 3)) (or (or (or ?v_1 (= x_4 1)) (= x_4 2)) (= x_4 3))) (not (< x_4 0))) (<= x_4 3)) (> x_6 0)) (>= x_6 0)) (>= x_7 0)) (>= x_8 0)) (>= x_9 0)) (>= x_13 0)) (or (or (or ?v_23 (= x_24 1)) (= x_24 2)) ?v_12)) (not (< x_24 0))) (<= x_24 3)) (or (or (or (= x_25 0) (= x_25 1)) (= x_25 2)) (= x_25 3))) (not (< x_25 0))) (<= x_25 3)) (or (or (or ?v_19 (= x_26 1)) (= x_26 2)) ?v_10)) (not (< x_26 0))) (<= x_26 3)) (or (or (or ?v_21 (= x_27 1)) (= x_27 2)) ?v_11)) (not (< x_27 0))) (<= x_27 3)) (>= x_28 0)) (>= x_38 0)) (>= x_39 0)) (>= x_42 0)) (>= x_43 0)) (>= x_44 0)) (>= x_47 0)) (>= x_50 0)) (>= x_51 0)) (not (<= x_52 (* x_6 3)))) (>= x_52 0)) (>= x_54 0)) (>= x_55 0)) (>= x_56 0)) (or (or ?v_67 x_1) (and (or (not ?v_0) ?v_8) (or (not ?v_1) ?v_9)))) (= x_40 (ite x_21 2 1))) (= x_41 (ite x_3 1 2))) (= x_45 ?v_2)) (= x_46 ?v_2)) (= x_48 (+ (ite ?v_5 (ite ?v_4 ?v_6 x_45) (ite ?v_4 x_45 ?v_7)) x_25))) (= x_49 (+ (ite ?v_5 (ite ?v_4 ?v_6 x_46) (ite ?v_4 x_46 ?v_7)) x_25))) (or (or (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and ?v_13 ?v_14) ?v_36) ?v_15) ?v_16) (= x_24 (ite ?v_17 (ite (not (< x_48 3)) 3 x_48) x_25))) (= x_16 ?v_18)) (= x_17 ?v_20)) (= x_14 ?v_22)) ?v_49) ?v_24) (and (and (and (and (and (and (and (and (and (and ?v_13 (not ?v_14)) x_29) (= x_9 x_13)) ?v_15) ?v_16) (= x_24 (ite ?v_17 (ite (not (< x_49 3)) 3 x_49) x_25))) (= x_16 (or ?v_18 ?v_19))) (= x_17 (or ?v_20 ?v_21))) (= x_14 (or ?v_22 ?v_23))) ?v_24)) ?v_47) ?v_48) ?v_65) ?v_50) ?v_51) ?v_52) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_40 (or (or (and (and (and ?v_25 ?v_8) ?v_33) ?v_29) (and (and (and ?v_26 ?v_9) ?v_34) ?v_31)) (and (and ?v_17 ?v_35) ?v_32))) (not x_36)) (or (or (or (or ?v_28 ?v_41) x_33) x_3) (not (< x_9 x_42)))) (or (or (or (or ?v_30 ?v_42) x_35) x_5) (not (< x_9 x_43)))) (or (or (or ?v_43 x_31) x_15) (not (< x_9 x_39)))) (or (or (or (and (and (and (and ?v_33 ?v_8) ?v_29) ?v_53) ?v_54) (and (and (and (and ?v_34 ?v_9) ?v_31) ?v_55) ?v_56)) (and (and (and (and ?v_35 ?v_17) ?v_32) ?v_57) ?v_58)) (and (< x_8 ?v_44) ?v_36))) (= x_32 (or x_33 ?v_37))) (= x_34 (or x_35 ?v_38))) (= x_30 (or x_31 ?v_39))) ?v_45) ?v_46) (and (and (and (and (and (and (and (and (and ?v_40 (or (or (or ?v_28 x_33) x_3) ?v_41)) (or (or (or ?v_30 x_35) x_5) ?v_42)) (or (or x_31 x_15) ?v_43)) x_36) (= x_9 ?v_44)) ?v_45) ?v_46) ?v_47) ?v_48)) ?v_63) ?v_64) ?v_24) ?v_49) ?v_50) ?v_51) ?v_52)) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_59 ?v_60) (not x_10)) (or (or (or ?v_28 x_21) x_3) (<= x_9 x_42))) (or (or (or ?v_30 x_23) x_5) (<= x_9 x_43))) (or (or x_19 x_15) (<= x_9 x_39))) (or (or (or (and (and (and (and (not x_21) ?v_8) (< x_7 x_42)) ?v_53) ?v_54) (and (and (and (and (not x_23) ?v_9) (< x_7 x_43)) ?v_55) ?v_56)) (and (and (and (not x_19) ?v_17) ?v_57) ?v_58)) ?v_36)) (= x_20 (or x_21 (= x_42 x_9)))) (= x_22 (or x_23 (= x_43 x_9)))) (= x_18 (or x_19 (= x_39 x_9)))) ?v_61) ?v_62) (and (and (and (and (and (and (and ?v_59 (not ?v_60)) x_10) ?v_61) ?v_62) (= x_9 x_7)) ?v_50) ?v_51)) ?v_63) ?v_64) ?v_24) ?v_49) ?v_47) ?v_48) ?v_65))) (or (or (and ?v_66 (= x_12 (ite (not x_1) x_0 1))) (and ?v_68 (= x_12 (ite (not x_37) x_0 2)))) (and (and ?v_67 (not ?v_68)) (= x_12 x_0)))) (or (and (and ?v_69 (not (<= x_38 x_50))) (not (<= x_50 ?v_70))) (and ?v_71 (= x_50 x_42)))) (or (and (and ?v_69 (not (<= x_38 x_51))) (not (<= x_51 ?v_70))) (and ?v_71 (= x_51 x_43)))) (or (and (and ?v_69 (= x_38 (+ x_8 x_52))) x_53) (and (and ?v_71 (not x_53)) (= x_38 x_8)))) (or (and (and (and (and ?v_39 (not (<= x_54 x_9))) (not (<= x_55 x_9))) (< x_54 x_55)) (< x_55 x_56)) (and (and (and (not ?v_39) (= x_54 x_39)) (= x_55 x_44)) (= x_56 x_47)))) ?v_13) (not x_29)) (or (and ?v_19 x_16) (and ?v_21 x_17))))))))))))
(check-sat)
(exit)