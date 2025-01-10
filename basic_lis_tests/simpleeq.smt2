(set-logic QF_LIA)

(declare-fun x () Int)
(declare-const y Int)
(assert (= x 7))
(assert (= y -4))
(check-sat)
