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
(declare-fun x_2 () Bool)
(declare-fun x_3 () Bool)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Bool)
(declare-fun x_9 () Bool)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Bool)
(declare-fun x_13 () Bool)
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
(declare-fun x_29 () Real)
(declare-fun x_30 () Real)
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
(assert (let ((?v_27 (+ x_4 x_5)) (?v_67 (<= x_6 x_7)) (?v_50 (= x_8 x_9)) (?v_9 (= x_10 0)) (?v_10 (< x_6 x_11)) (?v_34 (= x_7 x_6)) (?v_57 (= x_10 2)) (?v_59 (= x_12 x_13)) (?v_60 (and (= x_14 x_15) (= x_16 x_17))) (?v_48 (= x_18 x_19)) (?v_49 (and (= x_20 x_21) (= x_22 x_23))) (?v_61 (= x_24 x_25)) (?v_62 (and (= x_26 x_27) (= x_28 x_29))) (?v_20 (= x_30 x_11)) (?v_47 (= x_31 x_32)) (?v_45 (= x_33 x_3)) (?v_46 (and (= x_34 x_1) (= x_35 x_2))) (?v_63 (= x_36 x_37)) (?v_68 (- x_38 x_4)) (?v_38 (= x_10 1)) (?v_42 (+ x_5 x_4)) (?v_37 (<= x_39 x_7))) (let ((?v_44 (= x_12 (or x_13 (and ?v_37 x_3)))) (?v_30 (<= x_42 ?v_27)) (?v_32 (<= x_43 ?v_27)) (?v_29 (<= x_42 x_5)) (?v_31 (<= x_43 x_5)) (?v_22 (not x_15)) (?v_51 (< x_42 x_6)) (?v_52 (= x_7 x_42)) (?v_25 (not x_17)) (?v_53 (< x_43 x_6)) (?v_54 (= x_7 x_43)) (?v_13 (not x_13)) (?v_69 (not ?v_67)) (?v_23 (not x_1)) (?v_26 (not x_2)) (?v_28 (not x_3))) (let ((?v_21 (not ?v_29))) (let ((?v_35 (and ?v_21 (<= x_42 x_7))) (?v_24 (not ?v_31))) (let ((?v_36 (and ?v_24 (<= x_43 x_7)))) (let ((?v_43 (and (= x_14 (or x_15 (and ?v_35 x_1))) (= x_16 (or x_17 (and ?v_36 x_2))))) (?v_33 (<= x_39 ?v_27)) (?v_55 (< x_39 x_6)) (?v_56 (= x_7 x_39)) (?v_39 (not ?v_30)) (?v_40 (not ?v_32)) (?v_1 (and (not (<= x_39 x_5)) ?v_37)) (?v_2 (and (not (<= x_44 x_5)) (<= x_44 x_7)))) (let ((?v_41 (not ?v_33)) (?v_19 (= x_24 0)) (?v_8 (= x_24 3)) (?v_15 (= x_26 0)) (?v_6 (= x_26 3)) (?v_17 (= x_28 0)) (?v_7 (= x_28 3)) (?v_64 (= x_0 0))) (let ((?v_65 (not ?v_64)) (?v_3 (and (not (<= x_47 x_5)) (<= x_47 x_7))) (?v_11 (= x_26 (ite ?v_22 (ite (and ?v_35 (< x_27 3)) (+ x_27 1) x_27) x_27))) (?v_12 (= x_28 (ite ?v_25 (ite (and ?v_36 (< x_29 3)) (+ x_29 1) x_29) x_29))) (?v_14 (or x_15 ?v_6)) (?v_16 (or x_17 ?v_7)) (?v_18 (or x_13 ?v_8)) (?v_66 (= x_0 1)) (?v_0 (ite ?v_1 2 1)) (?v_4 (ite ?v_1 3 2)) (?v_5 (ite ?v_1 1 0)) (?v_58 (<= (ite x_19 (ite x_23 (ite x_21 3 2) x_40) (ite x_23 x_40 (ite x_21 1 0))) (* (* (ite x_13 (ite x_17 (ite x_15 0 1) x_41) (ite x_17 x_41 (ite x_15 2 3))) 1) (/ 1 2))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_10 2) (>= x_10 0)) (<= x_0 2)) (>= x_0 0)) (> x_4 0)) (>= x_4 0)) (>= x_5 0)) (>= x_6 0)) (>= x_7 0)) (>= x_11 0)) (or (or (or ?v_19 (= x_24 1)) (= x_24 2)) ?v_8)) (not (< x_24 0))) (<= x_24 3)) (or (or (or (= x_25 0) (= x_25 1)) (= x_25 2)) (= x_25 3))) (not (< x_25 0))) (<= x_25 3)) (or (or (or ?v_15 (= x_26 1)) (= x_26 2)) ?v_6)) (not (< x_26 0))) (<= x_26 3)) (or (or (or (= x_27 0) (= x_27 1)) (= x_27 2)) (= x_27 3))) (not (< x_27 0))) (<= x_27 3)) (or (or (or ?v_17 (= x_28 1)) (= x_28 2)) ?v_7)) (not (< x_28 0))) (<= x_28 3)) (or (or (or (= x_29 0) (= x_29 1)) (= x_29 2)) (= x_29 3))) (not (< x_29 0))) (<= x_29 3)) (>= x_30 0)) (>= x_38 0)) (>= x_39 0)) (>= x_42 0)) (>= x_43 0)) (>= x_44 0)) (>= x_47 0)) (>= x_50 0)) (>= x_51 0)) (not (<= x_52 (* x_4 3)))) (>= x_52 0)) (>= x_54 0)) (>= x_55 0)) (>= x_56 0)) (or ?v_65 (and (and ?v_23 ?v_26) ?v_28))) (= x_40 (ite x_21 2 1))) (= x_41 (ite x_15 1 2))) (= x_45 ?v_0)) (= x_46 ?v_0)) (= x_48 (+ (ite ?v_3 (ite ?v_2 ?v_4 x_45) (ite ?v_2 x_45 ?v_5)) x_25))) (= x_49 (+ (ite ?v_3 (ite ?v_2 ?v_4 x_46) (ite ?v_2 x_46 ?v_5)) x_25))) (or (or (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and ?v_9 ?v_10) ?v_34) ?v_11) ?v_12) (= x_24 (ite ?v_13 (ite (not (< x_48 3)) 3 x_48) x_25))) (= x_14 ?v_14)) (= x_16 ?v_16)) (= x_12 ?v_18)) ?v_47) ?v_20) (and (and (and (and (and (and (and (and (and (and ?v_9 (not ?v_10)) x_31) (= x_7 x_11)) ?v_11) ?v_12) (= x_24 (ite ?v_13 (ite (not (< x_49 3)) 3 x_49) x_25))) (= x_14 (or ?v_14 ?v_15))) (= x_16 (or ?v_16 ?v_17))) (= x_12 (or ?v_18 ?v_19))) ?v_20)) ?v_45) ?v_46) ?v_63) ?v_48) ?v_49) ?v_50) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_38 (or (or (and (and (and ?v_21 ?v_22) ?v_23) ?v_30) (and (and (and ?v_24 ?v_25) ?v_26) ?v_32)) (and (and ?v_13 ?v_28) ?v_33))) (not x_36)) (or (or (or (or ?v_29 ?v_39) x_1) x_15) (not (< x_7 x_42)))) (or (or (or (or ?v_31 ?v_40) x_2) x_17) (not (< x_7 x_43)))) (or (or (or ?v_41 x_3) x_13) (not (< x_7 x_39)))) (or (or (or (and (and (and (and ?v_23 ?v_22) ?v_30) ?v_51) ?v_52) (and (and (and (and ?v_26 ?v_25) ?v_32) ?v_53) ?v_54)) (and (and (and (and ?v_28 ?v_13) ?v_33) ?v_55) ?v_56)) (and (< x_6 ?v_42) ?v_34))) (= x_34 (or x_1 ?v_35))) (= x_35 (or x_2 ?v_36))) (= x_33 (or x_3 ?v_37))) ?v_43) ?v_44) (and (and (and (and (and (and (and (and (and ?v_38 (or (or (or ?v_29 x_1) x_15) ?v_39)) (or (or (or ?v_31 x_2) x_17) ?v_40)) (or (or x_3 x_13) ?v_41)) x_36) (= x_7 ?v_42)) ?v_43) ?v_44) ?v_45) ?v_46)) ?v_61) ?v_62) ?v_20) ?v_47) ?v_48) ?v_49) ?v_50)) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_57 ?v_58) (not x_8)) (or (or (or ?v_29 x_21) x_15) (<= x_7 x_42))) (or (or (or ?v_31 x_23) x_17) (<= x_7 x_43))) (or (or x_19 x_13) (<= x_7 x_39))) (or (or (or (and (and (and (and (not x_21) ?v_22) (< x_5 x_42)) ?v_51) ?v_52) (and (and (and (and (not x_23) ?v_25) (< x_5 x_43)) ?v_53) ?v_54)) (and (and (and (not x_19) ?v_13) ?v_55) ?v_56)) ?v_34)) (= x_20 (or x_21 (= x_42 x_7)))) (= x_22 (or x_23 (= x_43 x_7)))) (= x_18 (or x_19 (= x_39 x_7)))) ?v_59) ?v_60) (and (and (and (and (and (and (and ?v_57 (not ?v_58)) x_8) ?v_59) ?v_60) (= x_7 x_5)) ?v_48) ?v_49)) ?v_61) ?v_62) ?v_20) ?v_47) ?v_45) ?v_46) ?v_63))) (or (or (and ?v_64 (= x_10 (ite (not x_32) x_0 1))) (and ?v_66 (= x_10 (ite (not x_37) x_0 2)))) (and (and ?v_65 (not ?v_66)) (= x_10 x_0)))) (or (and (and ?v_67 (not (<= x_38 x_50))) (not (<= x_50 ?v_68))) (and ?v_69 (= x_50 x_42)))) (or (and (and ?v_67 (not (<= x_38 x_51))) (not (<= x_51 ?v_68))) (and ?v_69 (= x_51 x_43)))) (or (and (and ?v_67 (= x_38 (+ x_6 x_52))) x_53) (and (and ?v_69 (not x_53)) (= x_38 x_6)))) (or (and (and (and (and ?v_37 (not (<= x_54 x_7))) (not (<= x_55 x_7))) (< x_54 x_55)) (< x_55 x_56)) (and (and (and (not ?v_37) (= x_54 x_39)) (= x_55 x_44)) (= x_56 x_47)))) ?v_9) (or (or x_34 x_35) x_33)))))))))))
(check-sat)
(exit)