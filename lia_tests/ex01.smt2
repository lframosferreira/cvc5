(set-logic LIA)
(declare-fun y () Int)
(assert
  (exists ((x Int))
    (= (+ (* 1 y) (* 1 x)) 4)
  )
)
(check-sat)
