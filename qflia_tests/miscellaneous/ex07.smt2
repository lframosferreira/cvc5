(set-logic LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert
  (not
    (<= (+ (* 2 x) (* (- 1) y)) 0)
  )
)
(check-sat)
