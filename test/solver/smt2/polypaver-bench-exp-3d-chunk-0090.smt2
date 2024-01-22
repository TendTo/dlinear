(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The meti-tarski benchmarks are proof obligations extracted from the
Meti-Tarski project, see:

  B. Akbarpour and L. C. Paulson. MetiTarski: An automatic theorem prover
  for real-valued special functions. Journal of Automated Reasoning,
  44(3):175-205, 2010.

Submitted by Dejan Jovanovic for SMT-LIB.


|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun skoZ () Real)
(declare-fun skoY () Real)
(declare-fun skoX () Real)
(assert (let ((?v_0 (* skoX (- 1))) (?v_1 (* skoY (- 1)))) (let ((?v_2 (+ (+ 2 ?v_0) ?v_1))) (and (<= (+ ?v_0 ?v_1) skoZ) (and (not (<= skoZ (+ (+ 7 ?v_0) ?v_1))) (and (<= 0 skoX) (and (<= 0 skoY) (and (<= 0 skoZ) (and (<= skoX 1) (and (<= skoY 1) (and (<= skoZ 1) (and (<= skoZ ?v_2) (<= ?v_2 skoZ)))))))))))))
(check-sat)
(exit)
