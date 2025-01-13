(set-logic LIA)
(declare-fun P () Int)
(assert
    (not
     (exists ((R Int))
      (not
       (or
        (exists ((x2 Int) (x3 Int))
         (not
          (or
           (not
            (and
             (<= (* (- 1) x2) 0)
             (<= (* (- 1) x3) 0)
            )
           )
           (not
            (= (+ (* (- 1) R) (* 3 x2) (* 5 x3)) 0)
           )
          )
         )
        )
        (<= (+ (* (- 1) P) (* 1 R)) 0)
       )
      )
      )
      )
  )
(check-sat)
