(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x 4))
(assert (= y 7))
(check-sat)
