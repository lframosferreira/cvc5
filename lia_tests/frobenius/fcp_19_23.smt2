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
              (= (+ (* (- 1) P) (* 19 x0) (* 23 x1)) 0)
            )
          )
        )
      )
    )
    (not
      (exists ((R Int))
        (not
          (or
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
                    (= (+ (* (- 1) R) (* 19 x0) (* 23 x1)) 0)
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

