(set-logic LIA)
(declare-fun P () Int)
(declare-fun T () Int)
 (assert
  (and
   (<= (* (- 1) P) 0)
   (not
    (exists ((x0 Int) (x1 Int))
     (and 
      (not
       (or
        (not
         (and
          (<= (* (- 1) x0) 0)
          (<= (* (- 1) x1) 0)
         )
        )
        (not
         (= (+ (* (- 1) P) (* 3 x0) (* 5 x1)) 0)
        )
       )
      )
     )
    )
   )
   (= T 7)
   )
 )
(check-sat)
