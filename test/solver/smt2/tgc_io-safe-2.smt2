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
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)
(declare-fun x_10 () Real)
(declare-fun x_11 () Bool)
(declare-fun x_12 () Bool)
(declare-fun x_13 () Real)
(declare-fun x_14 () Bool)
(declare-fun x_15 () Bool)
(declare-fun x_16 () Bool)
(declare-fun x_17 () Bool)
(declare-fun x_18 () Bool)
(declare-fun x_19 () Bool)
(declare-fun x_20 () Bool)
(declare-fun x_21 () Real)
(declare-fun x_22 () Bool)
(declare-fun x_23 () Bool)
(declare-fun x_24 () Real)
(declare-fun x_25 () Real)
(declare-fun x_26 () Real)
(declare-fun x_27 () Bool)
(declare-fun x_28 () Bool)
(declare-fun x_29 () Real)
(declare-fun x_30 () Bool)
(declare-fun x_31 () Bool)
(declare-fun x_32 () Real)
(declare-fun x_33 () Real)
(declare-fun x_34 () Bool)
(declare-fun x_35 () Bool)
(declare-fun x_36 () Real)
(declare-fun x_37 () Bool)
(declare-fun x_38 () Bool)
(declare-fun x_39 () Bool)
(declare-fun x_40 () Bool)
(declare-fun x_41 () Bool)
(declare-fun x_42 () Bool)
(declare-fun x_43 () Real)
(declare-fun x_44 () Bool)
(declare-fun x_45 () Bool)
(declare-fun x_46 () Real)
(declare-fun x_47 () Real)
(declare-fun x_48 () Real)
(declare-fun x_49 () Real)
(declare-fun x_50 () Real)
(assert (let ((?v_32 (+ x_13 x_7)) (?v_23 (+ x_24 x_7)) (?v_26 (= x_33 x_9)) (?v_2 (not x_34))) (let ((?v_4 (and ?v_2 x_35)) (?v_31 (= x_36 x_13)) (?v_24 (and (= x_37 x_14) (= x_38 x_15))) (?v_9 (= x_25 1)) (?v_33 (and (= x_39 x_17) (= x_40 x_18))) (?v_12 (and (= x_41 x_19) (= x_42 x_20))) (?v_5 (= x_43 x_21)) (?v_14 (not x_44))) (let ((?v_16 (and ?v_14 x_45)) (?v_17 (= x_46 0)) (?v_21 (= x_46 x_24)) (?v_0 (= x_25 0)) (?v_11 (+ x_21 x_7)) (?v_28 (= x_36 0)) (?v_42 (+ 0 x_6)) (?v_54 (= x_9 x_10)) (?v_37 (not x_11))) (let ((?v_39 (and ?v_37 x_12)) (?v_55 (= x_13 0)) (?v_51 (and (= x_14 x_2) (= x_15 x_3))) (?v_56 (and (= x_17 x_4) (= x_18 x_5))) (?v_43 (and (= x_19 x_0) (= x_20 x_1))) (?v_38 (= x_21 0)) (?v_46 (not x_22))) (let ((?v_48 (and ?v_46 x_23)) (?v_47 (= x_24 0)) (?v_36 (not x_16)) (?v_34 (not x_0)) (?v_35 (not x_1)) (?v_44 (not x_2)) (?v_45 (not x_3)) (?v_52 (not x_4)) (?v_53 (not x_5)) (?v_3 (not x_19)) (?v_1 (not x_20)) (?v_6 (not x_35)) (?v_8 (not x_42)) (?v_7 (not x_41)) (?v_15 (not x_14)) (?v_13 (not x_15)) (?v_20 (not x_38)) (?v_18 (not x_45)) (?v_19 (not x_37)) (?v_27 (not x_17)) (?v_25 (not x_18)) (?v_30 (not x_40)) (?v_29 (not x_39)) (?v_40 (not x_12)) (?v_49 (not x_23)) (?v_10 (<= ?v_11 5)) (?v_22 (<= ?v_23 1)) (?v_41 (<= ?v_42 5)) (?v_50 (<= ?v_42 1))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_47 1) (>= x_47 0)) (<= x_25 1)) (>= x_25 0)) (and ?v_34 ?v_35)) (and ?v_44 ?v_45)) (and ?v_52 ?v_53)) (not (< x_8 0))) (not (< x_7 0))) (not (< x_6 0))) (= x_47 (ite ?v_9 0 1))) (or (or (or (or (or (and (and (and (and (and (and (and (and (= x_48 0) ?v_0) ?v_3) ?v_1) ?v_2) ?v_6) x_41) ?v_8) (= x_43 0)) (and (and (and (and (and (and (and (and (= x_48 1) ?v_0) x_19) ?v_1) (not (<= x_21 2))) ?v_4) ?v_7) x_42) ?v_5)) (and (and (and (and (and (and (and (= x_48 2) ?v_0) ?v_3) x_20) ?v_4) x_41) x_42) ?v_5)) (and (and (and (and (and (and (and (and (= x_48 3) ?v_0) x_19) x_20) x_34) ?v_6) ?v_7) ?v_8) ?v_5)) (and (and (and (and (and (and (and (and (= x_48 4) ?v_9) (or (or ?v_3 x_20) ?v_10)) (or (or x_19 ?v_1) ?v_10)) (or (or ?v_3 ?v_1) ?v_10)) (= x_43 ?v_11)) (= x_34 x_11)) (= x_35 x_12)) ?v_12)) (and (and (and (and (= x_48 5) ?v_0) ?v_5) ?v_4) ?v_12))) (or (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_49 0) ?v_0) ?v_15) ?v_13) ?v_2) ?v_6) ?v_16) x_37) ?v_20) ?v_17) (and (and (and (and (and (and (and (and (and (= x_49 1) ?v_0) x_14) ?v_13) (= x_24 1)) ?v_14) ?v_18) ?v_19) x_38) ?v_21)) (and (and (and (and (and (and (and (and (and (= x_49 2) ?v_0) ?v_15) x_15) x_34) ?v_6) ?v_16) x_37) x_38) ?v_17)) (and (and (and (and (and (and (and (and (= x_49 3) ?v_0) x_14) x_15) x_44) ?v_18) ?v_19) ?v_20) ?v_21)) (and (and (and (and (and (and (and (= x_49 4) ?v_9) (or (or ?v_15 x_15) ?v_22)) (or (or ?v_15 ?v_13) ?v_22)) (= x_46 ?v_23)) (= x_44 x_22)) (= x_45 x_23)) ?v_24)) (and (and (and (and (and (and (= x_49 5) ?v_0) ?v_2) x_35) ?v_21) ?v_16) ?v_24))) (or (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_50 0) ?v_0) ?v_27) ?v_25) ?v_14) ?v_18) x_39) ?v_30) ?v_28) ?v_26) (and (and (and (and (and (and (and (= x_50 1) ?v_0) x_17) ?v_25) ?v_29) x_40) ?v_26) ?v_31)) (and (and (and (and (and (and (and (and (and (= x_50 2) ?v_0) ?v_27) x_18) x_44) ?v_18) x_39) x_40) ?v_28) ?v_26)) (and (and (and (and (and (and (and (and (= x_50 3) ?v_0) x_17) x_18) (not (< x_13 1))) ?v_29) ?v_30) ?v_26) ?v_31)) (and (and (and (and (and (and (= x_50 4) ?v_9) (or (or ?v_27 x_18) (<= ?v_32 1))) (or (or ?v_27 ?v_25) (<= ?v_32 2))) (= x_36 ?v_32)) ?v_33) ?v_26)) (and (and (and (and (and (and (= x_50 5) ?v_0) ?v_14) x_45) ?v_31) ?v_33) ?v_26))) (= x_25 (ite x_16 0 1))) (or (or (or (or (or (and (and (and (and (and (and (and (and (= x_26 0) ?v_36) ?v_34) ?v_35) ?v_37) ?v_40) x_19) ?v_1) ?v_38) (and (and (and (and (and (and (and (and (= x_26 1) ?v_36) x_0) ?v_35) (not (<= 0 2))) ?v_39) ?v_3) x_20) ?v_38)) (and (and (and (and (and (and (and (= x_26 2) ?v_36) ?v_34) x_1) ?v_39) x_19) x_20) ?v_38)) (and (and (and (and (and (and (and (and (= x_26 3) ?v_36) x_0) x_1) x_11) ?v_40) ?v_3) ?v_1) ?v_38)) (and (and (and (and (and (and (and (and (= x_26 4) x_16) (or (or ?v_34 x_1) ?v_41)) (or (or x_0 ?v_35) ?v_41)) (or (or ?v_34 ?v_35) ?v_41)) (= x_21 ?v_42)) (= x_11 x_27)) (= x_12 x_28)) ?v_43)) (and (and (and (and (= x_26 5) ?v_36) ?v_38) ?v_39) ?v_43))) (or (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_29 0) ?v_36) ?v_44) ?v_45) ?v_37) ?v_40) ?v_48) x_14) ?v_13) ?v_47) (and (and (and (and (and (and (and (and (and (= x_29 1) ?v_36) x_2) ?v_45) (= 0 1)) ?v_46) ?v_49) ?v_15) x_15) ?v_47)) (and (and (and (and (and (and (and (and (and (= x_29 2) ?v_36) ?v_44) x_3) x_11) ?v_40) ?v_48) x_14) x_15) ?v_47)) (and (and (and (and (and (and (and (and (= x_29 3) ?v_36) x_2) x_3) x_22) ?v_49) ?v_15) ?v_13) ?v_47)) (and (and (and (and (and (and (and (= x_29 4) x_16) (or (or ?v_44 x_3) ?v_50)) (or (or ?v_44 ?v_45) ?v_50)) (= x_24 ?v_42)) (= x_22 x_30)) (= x_23 x_31)) ?v_51)) (and (and (and (and (and (and (= x_29 5) ?v_36) ?v_37) x_12) ?v_47) ?v_48) ?v_51))) (or (or (or (or (or (and (and (and (and (and (and (and (and (and (= x_32 0) ?v_36) ?v_52) ?v_53) ?v_46) ?v_49) x_17) ?v_25) ?v_55) ?v_54) (and (and (and (and (and (and (and (= x_32 1) ?v_36) x_4) ?v_53) ?v_27) x_18) ?v_54) ?v_55)) (and (and (and (and (and (and (and (and (and (= x_32 2) ?v_36) ?v_52) x_5) x_22) ?v_49) x_17) x_18) ?v_55) ?v_54)) (and (and (and (and (and (and (and (and (= x_32 3) ?v_36) x_4) x_5) (not (< 0 1))) ?v_27) ?v_25) ?v_54) ?v_55)) (and (and (and (and (and (and (= x_32 4) x_16) (or (or ?v_52 x_5) ?v_50)) (or (or ?v_52 ?v_53) (<= ?v_42 2))) (= x_13 ?v_42)) ?v_56) ?v_54)) (and (and (and (and (and (and (= x_32 5) ?v_36) ?v_46) x_23) ?v_55) ?v_56) ?v_54))) (or (or (and (and ?v_7 x_42) (or x_39 ?v_30)) (and (and ?v_3 x_20) (or x_17 ?v_25))) (and (and ?v_34 x_1) (or x_4 ?v_53)))) (or ?v_40 ?v_37)) (or ?v_49 ?v_46)) (or (not x_28) (not x_27))) (or (not x_31) (not x_30))) (or ?v_6 ?v_2)) (or ?v_18 ?v_14))))))))
(check-sat)
(exit)
