(set-logic QF_LRA) ; use the logic of linear real arithmetic
(declare-fun x () Real) ; real variable definition
(declare-fun y () Real)
(declare-fun z () Real)
(declare-fun u () Real)
(declare-fun v () Real)
(assert (and (or (<= (+ 3 x) (* 2 y)) (>= (+ 4 x) z)) (<= 1 v)))
(check-sat) ; check if the formula is satisfiable
(get-model) ; print the model, if possible

