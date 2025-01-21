; (set-logic QF_LIA)
;
; (declare-fun x () Int)
; (declare-fun y () Int)
; (declare-fun z () Int)
; (assert (<= (+ x (* 2 y)) 1))
; (assert (= (+ (+ (* 3 z) (+ (* 7 x) 5)) (* 2 y)) 1))
; (check-sat)

(set-logic LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert
  (and
    (<= (+ (* 1 x) (* 2 y)) 1)
    (= (+ (* 7 x) (* 2 y) (* 3 z)) (- 4))
  )
)
(check-sat)
(get-model)
