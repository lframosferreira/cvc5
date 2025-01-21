(set-logic LIA)
(declare-fun y () Int)
(assert
  (exists ((x Int))
    (and
      (= (* 1 x) 4)
      (= (+ (* (- 1) y) (* 1 x)) 12)
    )
  )
)
(check-sat)
