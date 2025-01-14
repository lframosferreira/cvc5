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
              (= (+ (* (- 1) P) (* 179 x0) (* 181 x1)) 0)
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
                    (= (+ (* (- 1) R) (* 179 x0) (* 181 x1)) 0)
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

