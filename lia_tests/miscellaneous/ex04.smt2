(set-logic LIA)
(declare-fun y () Int)
(assert
  (exists ((x Int))
    (and
      (= (* 1 x) 7)
      (= (* 1 y) (- 4))
    )
  )
)
(check-sat)
