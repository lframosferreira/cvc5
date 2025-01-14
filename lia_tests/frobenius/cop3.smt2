(set-logic LIA)
(declare-fun P () Int)
(declare-fun T () Int)
 (assert
  (and
   (<= (* (- 1) P) 0)
   (= T 7)
   )
 )
(check-sat)
