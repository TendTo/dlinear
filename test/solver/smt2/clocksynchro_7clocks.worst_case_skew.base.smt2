(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source | Clock Synchronization. Bruno Dutertre (bruno@csl.sri.com) |)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun x_0 () Real)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Real)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Real)
(assert (let ((?v_0 (+ x_0 (/ 999 1000))) (?v_1 (+ x_0 (/ 1001 1000))) (?v_2 (not (<= (- 1 1) (+ (+ (+ x_10 x_11) (* (* (+ x_12 x_9) 2) (/ 1 999))) (/ 2335 666)))))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (not (<= x_8 0)) (not (<= x_9 0))) (not (<= x_10 0))) (not (< x_11 (+ x_10 (* (* (+ (* (* x_9 1) (/ 1 2)) 1) 1001) (/ 1 999)))))) (< x_12 (- (* (* (- (- x_9 x_11) 1) 999) (/ 1 2)) 1))) (not (< x_12 (* (* (+ (+ (+ x_8 x_10) x_11) (/ 1501 1000)) 1001) (/ 1 999))))) (= x_0 0)) (<= ?v_0 x_1)) (<= x_1 ?v_1)) (<= ?v_0 x_2)) (<= x_2 ?v_1)) (<= ?v_0 x_3)) (<= x_3 ?v_1)) (<= ?v_0 x_4)) (<= x_4 ?v_1)) (<= ?v_0 x_5)) (<= x_5 ?v_1)) (<= ?v_0 x_6)) (<= x_6 ?v_1)) (<= ?v_0 x_7)) (<= x_7 ?v_1)) (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or (or ?v_2 ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2) ?v_2))))
(check-sat)
(exit)
