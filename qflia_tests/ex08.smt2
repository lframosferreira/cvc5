(set-logic QF_LIA)

(declare-fun x () Int)
(declare-fun y () Int)

(assert (= (mod (+ (* 1 x) (* 1 y)) 4) 1))

(check-sat)

