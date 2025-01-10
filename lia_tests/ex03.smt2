(set-logic LIA)
(declare-fun n () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(assert
  (and
    (not
      (exists ((a Int) (b Int))
        (and
          (<= (* (- 1) a) 0)
          (<= (* (- 1) b) 0)
          (= (+ (* 1 n) (* (- 17) a) (* (- 19) b)) 0)
        )
      )
    )
    (not
      (exists ((m Int))
        (not
          (or
            (exists ((a Int) (b Int))
              (and
                (<= (* (- 1) a) 0)
                (<= (* (- 1) b) 0)
                (= (+ (* 1 m) (* (- 17) a) (* (- 19) b)) 0)
              )
            )
            (<= (+ (* (- 1) n) (* 1 m)) 0)
          )
        )
      )
    )
  )
)
(check-sat)
