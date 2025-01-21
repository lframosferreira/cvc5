(set-logic LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert
  (exists ((reminder_0 Int))
    (and
      (<= (* (- 1) reminder_0) 0)
      (<= (* 1 reminder_0) 3)
      (= (* 1 reminder_0) 1)
      (= (mod (+ (* 1 x) (* 1 y) (* (- 1) reminder_0)) 4) 0)
    )
  )
)
(check-sat)
