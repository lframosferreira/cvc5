(set-logic AUFLIRA)
(set-info :smt-lib-version 2.6)
(set-info :category "industrial")
(set-info :status unsat)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun f (U) U)
(assert (and (not (= (f (f a)) a)) (forall ((x U)) (= (f x) x))))
(check-sat)
(exit)