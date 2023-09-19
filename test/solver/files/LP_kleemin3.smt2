(set-logic QF_LRA)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(assert (<= 0.0 x1))
(assert (<= 0.0 x2))
(assert (<= 0.0 x3))
(assert  (<= x1 1.0))
(assert  (<= (+ (* 20.0 x1) x2) 100.0))
(assert  (<= (+ (* 200.0 x1) (* 20.0 x2) x3) 10000.0))
(check-sat)