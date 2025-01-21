(set-logic QF_LIA)

(declare-fun x () Int)
(assert (<= x 4))
(check-sat)
