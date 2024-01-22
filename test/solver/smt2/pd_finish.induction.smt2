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
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Bool)
(declare-fun x_7 () Bool)
(declare-fun x_8 () Real)
(declare-fun x_9 () Bool)
(declare-fun x_10 () Bool)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Bool)
(declare-fun x_13 () Bool)
(declare-fun x_14 () Bool)
(declare-fun x_15 () Bool)
(declare-fun x_16 () Bool)
(declare-fun x_17 () Bool)
(declare-fun x_18 () Bool)
(declare-fun x_19 () Bool)
(declare-fun x_20 () Bool)
(declare-fun x_21 () Real)
(declare-fun x_22 () Real)
(declare-fun x_23 () Real)
(declare-fun x_24 () Real)
(declare-fun x_25 () Real)
(declare-fun x_26 () Real)
(declare-fun x_27 () Real)
(declare-fun x_28 () Bool)
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
(assert (let ((?v_25 (+ x_1 x_3)) (?v_66 (<= x_4 x_5)) (?v_50 (= x_6 x_7)) (?v_9 (= x_8 0)) (?v_10 (< x_4 x_0)) (?v_34 (= x_5 x_4)) (?v_57 (= x_8 2)) (?v_59 (= x_9 x_10)) (?v_60 (and (= x_11 x_12) (= x_13 x_14))) (?v_48 (= x_15 x_16)) (?v_49 (and (= x_17 x_18) (= x_19 x_20))) (?v_61 (= x_21 x_22)) (?v_62 (and (= x_23 x_24) (= x_25 x_26))) (?v_20 (= x_27 x_0)) (?v_47 (= x_28 x_29)) (?v_45 (= x_30 x_31)) (?v_46 (and (= x_32 x_33) (= x_34 x_35))) (?v_63 (= x_36 x_37)) (?v_67 (- x_38 x_1)) (?v_38 (= x_8 1)) (?v_42 (+ x_3 x_1)) (?v_37 (<= x_39 x_5))) (let ((?v_44 (= x_9 (or x_10 (and ?v_37 x_31)))) (?v_27 (<= x_42 ?v_25)) (?v_29 (<= x_43 ?v_25)) (?v_26 (<= x_42 x_3)) (?v_28 (<= x_43 x_3)) (?v_22 (not x_12)) (?v_51 (< x_42 x_4)) (?v_52 (= x_5 x_42)) (?v_24 (not x_14)) (?v_53 (< x_43 x_4)) (?v_54 (= x_5 x_43)) (?v_13 (not x_10)) (?v_68 (not ?v_66)) (?v_31 (not x_33)) (?v_32 (not x_35)) (?v_33 (not x_31))) (let ((?v_21 (not ?v_26))) (let ((?v_35 (and ?v_21 (<= x_42 x_5))) (?v_23 (not ?v_28))) (let ((?v_36 (and ?v_23 (<= x_43 x_5)))) (let ((?v_43 (and (= x_11 (or x_12 (and ?v_35 x_33))) (= x_13 (or x_14 (and ?v_36 x_35))))) (?v_30 (<= x_39 ?v_25)) (?v_55 (< x_39 x_4)) (?v_56 (= x_5 x_39)) (?v_39 (not ?v_27)) (?v_40 (not ?v_29)) (?v_1 (and (not (<= x_39 x_3)) ?v_37)) (?v_2 (and (not (<= x_44 x_3)) (<= x_44 x_5)))) (let ((?v_41 (not ?v_30)) (?v_19 (= x_21 0)) (?v_8 (= x_21 3)) (?v_15 (= x_23 0)) (?v_6 (= x_23 3)) (?v_17 (= x_25 0)) (?v_7 (= x_25 3)) (?v_3 (and (not (<= x_47 x_3)) (<= x_47 x_5))) (?v_11 (= x_23 (ite ?v_22 (ite (and ?v_35 (< x_24 3)) (+ x_24 1) x_24) x_24))) (?v_12 (= x_25 (ite ?v_24 (ite (and ?v_36 (< x_26 3)) (+ x_26 1) x_26) x_26)))) (let ((?v_14 (or x_12 ?v_6)) (?v_16 (or x_14 ?v_7)) (?v_18 (or x_10 ?v_8)) (?v_64 (= x_50 0)) (?v_65 (= x_50 1)) (?v_69 (+ (* x_2 2) x_1)) (?v_0 (ite ?v_1 2 1)) (?v_4 (ite ?v_1 3 2)) (?v_5 (ite ?v_1 1 0)) (?v_58 (<= (ite x_16 (ite x_20 (ite x_18 3 2) x_40) (ite x_20 x_40 (ite x_18 1 0))) (* (* (ite x_10 (ite x_14 (ite x_12 0 1) x_41) (ite x_14 x_41 (ite x_12 2 3))) 1) (/ 1 2))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_50 2) (>= x_50 0)) (<= x_8 2)) (>= x_8 0)) (>= x_0 0)) (> x_1 0)) (>= x_1 0)) (not (<= x_2 (* x_1 3)))) (>= x_2 0)) (>= x_3 0)) (>= x_4 0)) (>= x_5 0)) (or (or (or ?v_19 (= x_21 1)) (= x_21 2)) ?v_8)) (not (< x_21 0))) (<= x_21 3)) (or (or (or (= x_22 0) (= x_22 1)) (= x_22 2)) (= x_22 3))) (not (< x_22 0))) (<= x_22 3)) (or (or (or ?v_15 (= x_23 1)) (= x_23 2)) ?v_6)) (not (< x_23 0))) (<= x_23 3)) (or (or (or (= x_24 0) (= x_24 1)) (= x_24 2)) (= x_24 3))) (not (< x_24 0))) (<= x_24 3)) (or (or (or ?v_17 (= x_25 1)) (= x_25 2)) ?v_7)) (not (< x_25 0))) (<= x_25 3)) (or (or (or (= x_26 0) (= x_26 1)) (= x_26 2)) (= x_26 3))) (not (< x_26 0))) (<= x_26 3)) (>= x_27 0)) (>= x_38 0)) (>= x_39 0)) (>= x_42 0)) (>= x_43 0)) (>= x_44 0)) (>= x_47 0)) (>= x_51 0)) (>= x_52 0)) (>= x_54 0)) (>= x_55 0)) (>= x_56 0)) (< x_0 ?v_69)) (= x_40 (ite x_18 2 1))) (= x_41 (ite x_12 1 2))) (= x_45 ?v_0)) (= x_46 ?v_0)) (= x_48 (+ (ite ?v_3 (ite ?v_2 ?v_4 x_45) (ite ?v_2 x_45 ?v_5)) x_22))) (= x_49 (+ (ite ?v_3 (ite ?v_2 ?v_4 x_46) (ite ?v_2 x_46 ?v_5)) x_22))) (or (or (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and ?v_9 ?v_10) ?v_34) ?v_11) ?v_12) (= x_21 (ite ?v_13 (ite (not (< x_48 3)) 3 x_48) x_22))) (= x_11 ?v_14)) (= x_13 ?v_16)) (= x_9 ?v_18)) ?v_47) ?v_20) (and (and (and (and (and (and (and (and (and (and ?v_9 (not ?v_10)) x_28) (= x_5 x_0)) ?v_11) ?v_12) (= x_21 (ite ?v_13 (ite (not (< x_49 3)) 3 x_49) x_22))) (= x_11 (or ?v_14 ?v_15))) (= x_13 (or ?v_16 ?v_17))) (= x_9 (or ?v_18 ?v_19))) ?v_20)) ?v_45) ?v_46) ?v_63) ?v_48) ?v_49) ?v_50) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_38 (or (or (and (and (and ?v_21 ?v_22) ?v_31) ?v_27) (and (and (and ?v_23 ?v_24) ?v_32) ?v_29)) (and (and ?v_13 ?v_33) ?v_30))) (not x_36)) (or (or (or (or ?v_26 ?v_39) x_33) x_12) (not (< x_5 x_42)))) (or (or (or (or ?v_28 ?v_40) x_35) x_14) (not (< x_5 x_43)))) (or (or (or ?v_41 x_31) x_10) (not (< x_5 x_39)))) (or (or (or (and (and (and (and ?v_31 ?v_22) ?v_27) ?v_51) ?v_52) (and (and (and (and ?v_32 ?v_24) ?v_29) ?v_53) ?v_54)) (and (and (and (and ?v_33 ?v_13) ?v_30) ?v_55) ?v_56)) (and (< x_4 ?v_42) ?v_34))) (= x_32 (or x_33 ?v_35))) (= x_34 (or x_35 ?v_36))) (= x_30 (or x_31 ?v_37))) ?v_43) ?v_44) (and (and (and (and (and (and (and (and (and ?v_38 (or (or (or ?v_26 x_33) x_12) ?v_39)) (or (or (or ?v_28 x_35) x_14) ?v_40)) (or (or x_31 x_10) ?v_41)) x_36) (= x_5 ?v_42)) ?v_43) ?v_44) ?v_45) ?v_46)) ?v_61) ?v_62) ?v_20) ?v_47) ?v_48) ?v_49) ?v_50)) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_57 ?v_58) (not x_6)) (or (or (or ?v_26 x_18) x_12) (<= x_5 x_42))) (or (or (or ?v_28 x_20) x_14) (<= x_5 x_43))) (or (or x_16 x_10) (<= x_5 x_39))) (or (or (or (and (and (and (and (not x_18) ?v_22) (< x_3 x_42)) ?v_51) ?v_52) (and (and (and (and (not x_20) ?v_24) (< x_3 x_43)) ?v_53) ?v_54)) (and (and (and (not x_16) ?v_13) ?v_55) ?v_56)) ?v_34)) (= x_17 (or x_18 (= x_42 x_5)))) (= x_19 (or x_20 (= x_43 x_5)))) (= x_15 (or x_16 (= x_39 x_5)))) ?v_59) ?v_60) (and (and (and (and (and (and (and ?v_57 (not ?v_58)) x_6) ?v_59) ?v_60) (= x_5 x_3)) ?v_48) ?v_49)) ?v_61) ?v_62) ?v_20) ?v_47) ?v_45) ?v_46) ?v_63))) (or (or (and ?v_64 (= x_8 (ite (not x_29) x_50 1))) (and ?v_65 (= x_8 (ite (not x_37) x_50 2)))) (and (and (not ?v_64) (not ?v_65)) (= x_8 x_50)))) (or (and (and ?v_66 (not (<= x_38 x_51))) (not (<= x_51 ?v_67))) (and ?v_68 (= x_51 x_42)))) (or (and (and ?v_66 (not (<= x_38 x_52))) (not (<= x_52 ?v_67))) (and ?v_68 (= x_52 x_43)))) (or (and (and ?v_66 (= x_38 (+ x_4 x_2))) x_53) (and (and ?v_68 (not x_53)) (= x_38 x_4)))) (or (and (and (and (and ?v_37 (not (<= x_54 x_5))) (not (<= x_55 x_5))) (< x_54 x_55)) (< x_55 x_56)) (and (and (and (not ?v_37) (= x_54 x_39)) (= x_55 x_44)) (= x_56 x_47)))) (not (< x_27 ?v_69))))))))))))
(check-sat)
(exit)
