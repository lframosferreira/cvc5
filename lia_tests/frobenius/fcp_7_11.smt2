(set-logic LIA)
(declare-fun P () Int)
(assert
  (and
    (<= (* (- 1) P) 0)
    (not
      (exists ((x0 Int) (x1 Int))
        (not
          (or
            (not
              (and
                (<= (* (- 1) x0) 0)
                (<= (* (- 1) x1) 0)
              )
            )
            (not
              (= (+ (* (- 1) P) (* 7 x0) (* 11 x1)) 0)
            )
          )
        )
      )
    )
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
                    (= (+ (* (- 1) R) (* 7 x2) (* 11 x3)) 0)
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
)
(check-sat)
