; EXPECT: unsat
(set-logic ALL)
(set-option :incremental false)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(assert (= (+ (+ (+ (* (- 9) x0) (* 25 x1)) (* 0 x2)) (* 13 x3)) 17))
(assert (= (+ (+ (+ (* (- 6) x0) (* 32 x1)) (* 2 x2)) (* (- 32) x3)) (- 5)))
(assert (<= (+ (+ (+ (* 19 x0) (* 25 x1)) (* (- 32) x2)) (* (- 29) x3)) 14))
(assert (< (+ (+ (+ (* 6 x0) (* 22 x1)) (* (- 24) x2)) (* (- 6) x3)) (- 21)))
(assert (> (+ (+ (+ (* (- 18) x0) (* (- 21) x1)) (* (- 29) x2)) (* 12 x3)) 17))
(assert (> (+ (+ (+ (* (- 25) x0) (* (- 5) x1)) (* (- 22) x2)) (* (- 7) x3)) (- 21)))
(check-sat)