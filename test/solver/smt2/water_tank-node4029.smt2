(set-info :smt-lib-version 2.6)
(set-logic QF_LRA)
(set-info :source |
These benchmarks used in the paper:

  Dejan Jovanovic and Leonardo de Moura.  Solving Non-Linear Arithmetic.
  In IJCAR 2012, published as LNCS volume 7364, pp. 339--354.

The keymaera family contains VCs from Keymaera verification, see:

  A. Platzer, J.-D. Quesel, and P. Rummer.  Real world verification.
  In CADE 2009, pages 485-501. Springer, 2009.

Submitted by Dejan Jovanovic for SMT-LIB.

 KeYmaera example: water_tank, node 4029 For more info see: No further information available.
|)
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun stuscore2dollarskuscore0 () Real)
(declare-fun yuscore2dollarskuscore0 () Real)
(assert (not (=> (and (and (and (= yuscore2dollarskuscore0 10) (= stuscore2dollarskuscore0 0)) (>= yuscore2dollarskuscore0 1)) (<= yuscore2dollarskuscore0 12)) (or (or (= stuscore2dollarskuscore0 1) (= stuscore2dollarskuscore0 3)) (<= yuscore2dollarskuscore0 10)))))
(check-sat)
(exit)
