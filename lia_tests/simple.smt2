(set-logic QF_LIA)

(declare-fun x () Int)
; (declare-const y Int)
(assert (= x (- 3)))
(check-sat)
