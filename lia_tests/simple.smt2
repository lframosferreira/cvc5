(set-logic QF_LIA)

(declare-const x Int)
; (declare-const y Int)
(assert (= x 4))
(check-sat)
