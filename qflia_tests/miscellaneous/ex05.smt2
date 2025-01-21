(set-logic LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert
  (or
    (<= (* (- 1) x) (- 6))
    (<= (* 1 y) 9)
    (<= (* (- 1) z) 0)
    (= (+ (* 1 x) (* 1 y)) 15)
    (<= (+ (* 1 x) (* 1 z)) 20)
  )
)
(check-sat)

