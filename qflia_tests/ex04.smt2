(set-logic QF_LIA)

(declare-fun x () Int)

(assert (= (mod (+ (* 3 x) (- 7)) 2) 0))

(check-sat)
(get-model)
