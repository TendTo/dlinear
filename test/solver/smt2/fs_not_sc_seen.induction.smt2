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
(declare-fun x_5 () Bool)
(declare-fun x_6 () Bool)
(declare-fun x_7 () Bool)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Bool)
(declare-fun x_13 () Bool)
(declare-fun x_14 () Real)
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
(assert (let ((?v_26 (+ x_8 x_9)) (?v_72 (<= x_10 x_11)) (?v_51 (= x_12 x_13)) (?v_7 (= x_4 0)) (?v_11 (< x_10 x_14)) (?v_35 (= x_11 x_10)) (?v_61 (= x_4 2)) (?v_63 (= x_15 x_16)) (?v_64 (and (= x_17 x_18) (= x_19 x_20))) (?v_49 (= x_7 x_3)) (?v_50 (and (= x_5 x_1) (= x_6 x_2))) (?v_65 (= x_21 x_22)) (?v_66 (and (= x_23 x_24) (= x_25 x_26))) (?v_21 (= x_27 x_14)) (?v_48 (= x_28 x_29)) (?v_46 (= x_30 x_31)) (?v_47 (and (= x_32 x_33) (= x_34 x_35))) (?v_67 (= x_36 x_37)) (?v_73 (- x_38 x_8)) (?v_39 (= x_4 1)) (?v_43 (+ x_9 x_8)) (?v_38 (<= x_39 x_11))) (let ((?v_45 (= x_15 (or x_16 (and ?v_38 x_31)))) (?v_28 (<= x_42 ?v_26)) (?v_30 (<= x_43 ?v_26)) (?v_27 (<= x_42 x_9)) (?v_29 (<= x_43 x_9)) (?v_23 (not x_18)) (?v_53 (< x_42 x_10)) (?v_54 (= x_11 x_42)) (?v_25 (not x_20)) (?v_56 (< x_43 x_10)) (?v_57 (= x_11 x_43)) (?v_14 (not x_16)) (?v_74 (not ?v_72)) (?v_32 (not x_33)) (?v_33 (not x_35)) (?v_34 (not x_31))) (let ((?v_22 (not ?v_27))) (let ((?v_36 (and ?v_22 (<= x_42 x_11))) (?v_24 (not ?v_29))) (let ((?v_37 (and ?v_24 (<= x_43 x_11)))) (let ((?v_44 (and (= x_17 (or x_18 (and ?v_36 x_33))) (= x_19 (or x_20 (and ?v_37 x_35))))) (?v_31 (<= x_39 ?v_26)) (?v_59 (< x_39 x_10)) (?v_60 (= x_11 x_39)) (?v_40 (not ?v_28)) (?v_41 (not ?v_30)) (?v_2 (and (not (<= x_39 x_9)) ?v_38)) (?v_3 (and (not (<= x_44 x_9)) (<= x_44 x_11)))) (let ((?v_42 (not ?v_31)) (?v_20 (= x_21 0)) (?v_10 (= x_21 3)) (?v_16 (= x_23 0)) (?v_8 (= x_23 3)) (?v_18 (= x_25 0)) (?v_9 (= x_25 3)) (?v_69 (= x_0 1))) (let ((?v_71 (not ?v_69)) (?v_52 (not x_1)) (?v_55 (not x_2)) (?v_58 (not x_3))) (let ((?v_0 (and (and ?v_52 ?v_55) ?v_58)) (?v_68 (= x_0 0))) (let ((?v_70 (not ?v_68)) (?v_4 (and (not (<= x_47 x_9)) (<= x_47 x_11))) (?v_12 (= x_23 (ite ?v_23 (ite (and ?v_36 (< x_24 3)) (+ x_24 1) x_24) x_24))) (?v_13 (= x_25 (ite ?v_25 (ite (and ?v_37 (< x_26 3)) (+ x_26 1) x_26) x_26))) (?v_15 (or x_18 ?v_8)) (?v_17 (or x_20 ?v_9)) (?v_19 (or x_16 ?v_10)) (?v_1 (ite ?v_2 2 1)) (?v_5 (ite ?v_2 3 2)) (?v_6 (ite ?v_2 1 0)) (?v_62 (<= (ite x_3 (ite x_2 (ite x_1 3 2) x_40) (ite x_2 x_40 (ite x_1 1 0))) (* (* (ite x_16 (ite x_20 (ite x_18 0 1) x_41) (ite x_20 x_41 (ite x_18 2 3))) 1) (/ 1 2))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_4 2) (>= x_4 0)) (<= x_0 2)) (>= x_0 0)) (> x_8 0)) (>= x_8 0)) (>= x_9 0)) (>= x_10 0)) (>= x_11 0)) (>= x_14 0)) (or (or (or ?v_20 (= x_21 1)) (= x_21 2)) ?v_10)) (not (< x_21 0))) (<= x_21 3)) (or (or (or (= x_22 0) (= x_22 1)) (= x_22 2)) (= x_22 3))) (not (< x_22 0))) (<= x_22 3)) (or (or (or ?v_16 (= x_23 1)) (= x_23 2)) ?v_8)) (not (< x_23 0))) (<= x_23 3)) (or (or (or (= x_24 0) (= x_24 1)) (= x_24 2)) (= x_24 3))) (not (< x_24 0))) (<= x_24 3)) (or (or (or ?v_18 (= x_25 1)) (= x_25 2)) ?v_9)) (not (< x_25 0))) (<= x_25 3)) (or (or (or (= x_26 0) (= x_26 1)) (= x_26 2)) (= x_26 3))) (not (< x_26 0))) (<= x_26 3)) (>= x_27 0)) (>= x_38 0)) (>= x_39 0)) (>= x_42 0)) (>= x_43 0)) (>= x_44 0)) (>= x_47 0)) (>= x_50 0)) (>= x_51 0)) (not (<= x_52 (* x_8 3)))) (>= x_52 0)) (>= x_54 0)) (>= x_55 0)) (>= x_56 0)) (or ?v_71 ?v_0)) (or (not ?v_7) (and (and (not x_5) (not x_6)) (not x_7)))) (or ?v_70 ?v_0)) (= x_40 (ite x_1 2 1))) (= x_41 (ite x_18 1 2))) (= x_45 ?v_1)) (= x_46 ?v_1)) (= x_48 (+ (ite ?v_4 (ite ?v_3 ?v_5 x_45) (ite ?v_3 x_45 ?v_6)) x_22))) (= x_49 (+ (ite ?v_4 (ite ?v_3 ?v_5 x_46) (ite ?v_3 x_46 ?v_6)) x_22))) (or (or (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and ?v_7 ?v_11) ?v_35) ?v_12) ?v_13) (= x_21 (ite ?v_14 (ite (not (< x_48 3)) 3 x_48) x_22))) (= x_17 ?v_15)) (= x_19 ?v_17)) (= x_15 ?v_19)) ?v_48) ?v_21) (and (and (and (and (and (and (and (and (and (and ?v_7 (not ?v_11)) x_28) (= x_11 x_14)) ?v_12) ?v_13) (= x_21 (ite ?v_14 (ite (not (< x_49 3)) 3 x_49) x_22))) (= x_17 (or ?v_15 ?v_16))) (= x_19 (or ?v_17 ?v_18))) (= x_15 (or ?v_19 ?v_20))) ?v_21)) ?v_46) ?v_47) ?v_67) ?v_49) ?v_50) ?v_51) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_39 (or (or (and (and (and ?v_22 ?v_23) ?v_32) ?v_28) (and (and (and ?v_24 ?v_25) ?v_33) ?v_30)) (and (and ?v_14 ?v_34) ?v_31))) (not x_36)) (or (or (or (or ?v_27 ?v_40) x_33) x_18) (not (< x_11 x_42)))) (or (or (or (or ?v_29 ?v_41) x_35) x_20) (not (< x_11 x_43)))) (or (or (or ?v_42 x_31) x_16) (not (< x_11 x_39)))) (or (or (or (and (and (and (and ?v_32 ?v_23) ?v_28) ?v_53) ?v_54) (and (and (and (and ?v_33 ?v_25) ?v_30) ?v_56) ?v_57)) (and (and (and (and ?v_34 ?v_14) ?v_31) ?v_59) ?v_60)) (and (< x_10 ?v_43) ?v_35))) (= x_32 (or x_33 ?v_36))) (= x_34 (or x_35 ?v_37))) (= x_30 (or x_31 ?v_38))) ?v_44) ?v_45) (and (and (and (and (and (and (and (and (and ?v_39 (or (or (or ?v_27 x_33) x_18) ?v_40)) (or (or (or ?v_29 x_35) x_20) ?v_41)) (or (or x_31 x_16) ?v_42)) x_36) (= x_11 ?v_43)) ?v_44) ?v_45) ?v_46) ?v_47)) ?v_65) ?v_66) ?v_21) ?v_48) ?v_49) ?v_50) ?v_51)) (and (and (and (and (and (and (and (or (and (and (and (and (and (and (and (and (and (and (and ?v_61 ?v_62) (not x_12)) (or (or (or ?v_27 x_1) x_18) (<= x_11 x_42))) (or (or (or ?v_29 x_2) x_20) (<= x_11 x_43))) (or (or x_3 x_16) (<= x_11 x_39))) (or (or (or (and (and (and (and ?v_52 ?v_23) (< x_9 x_42)) ?v_53) ?v_54) (and (and (and (and ?v_55 ?v_25) (< x_9 x_43)) ?v_56) ?v_57)) (and (and (and ?v_58 ?v_14) ?v_59) ?v_60)) ?v_35)) (= x_5 (or x_1 (= x_42 x_11)))) (= x_6 (or x_2 (= x_43 x_11)))) (= x_7 (or x_3 (= x_39 x_11)))) ?v_63) ?v_64) (and (and (and (and (and (and (and ?v_61 (not ?v_62)) x_12) ?v_63) ?v_64) (= x_11 x_9)) ?v_49) ?v_50)) ?v_65) ?v_66) ?v_21) ?v_48) ?v_46) ?v_47) ?v_67))) (or (or (and ?v_68 (= x_4 (ite (not x_29) x_0 1))) (and ?v_69 (= x_4 (ite (not x_37) x_0 2)))) (and (and ?v_70 ?v_71) (= x_4 x_0)))) (or (and (and ?v_72 (not (<= x_38 x_50))) (not (<= x_50 ?v_73))) (and ?v_74 (= x_50 x_42)))) (or (and (and ?v_72 (not (<= x_38 x_51))) (not (<= x_51 ?v_73))) (and ?v_74 (= x_51 x_43)))) (or (and (and ?v_72 (= x_38 (+ x_10 x_52))) x_53) (and (and ?v_74 (not x_53)) (= x_38 x_10)))) (or (and (and (and (and ?v_38 (not (<= x_54 x_11))) (not (<= x_55 x_11))) (< x_54 x_55)) (< x_55 x_56)) (and (and (and (not ?v_38) (= x_54 x_39)) (= x_55 x_44)) (= x_56 x_47)))) ?v_39) (or (or x_5 x_6) x_7)))))))))))))
(check-sat)
(exit)
