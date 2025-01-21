(set-logic LIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(assert
  (and
    (or
      (<= (* (- 1) a) (- 11))
      (<= (* 1 b) 4)
    )
    (and
      (<= (* (- 1) c) 0)
      (<= (* 1 c) 20)
    )
    (or
      (and
        (= (* 1 d) 3)
        (<= (* (- 1) e) (- 8))
      )
      (and
        (<= (* 1 e) (- 3))
          (= (* 1 d) 3)
      )
    )
    (and
      (<= (+ (* (- 1) a) (* 1 b)) (- 1))
      (<= (+ (* (- 1) c) (* 1 d)) (- 1))
    )
    (= (+ (* 1 a) (* 1 b)) 15)
  )
)
(check-sat)
