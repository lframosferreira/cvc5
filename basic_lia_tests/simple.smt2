(set-logic QF_LIA)

(declare-fun x () Int)
; (declare-const y Int)
(assert (not (= x 4)))
(check-sat)
