(set-logic LIA)
(declare-fun n () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert
  (and
    (<= (* (- 1) x) 0)
    (<= (* (- 1) y) 0)
    (= (+ (* 1 n) (* (- 17) x) (* (- 19) y)) 0)
    (not
      (exists ((a Int) (b Int))
        (and
          (<= (* (- 1) a) 0)
          (<= (* (- 1) b) 0)
          (= (+ (* 1 n) (* (- 17) a) (* (- 19) b)) 0)
        )
      )
    )
  )
)
(check-sat)
