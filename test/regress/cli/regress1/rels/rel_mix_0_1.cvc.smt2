; EXPECT: sat
(set-option :incremental false)
(set-logic ALL)


(declare-fun x () (Set (Tuple Int Int)))
(declare-fun y () (Set (Tuple Int Int)))
(declare-fun r () (Set (Tuple Int Int)))
(declare-fun w () (Set (Tuple Int)))
(declare-fun z () (Set (Tuple Int)))
(declare-fun r2 () (Set (Tuple Int Int)))
(declare-fun d () (Tuple Int Int))
(assert (= d (tuple 1 3)))
(assert (set.member (tuple 1 3) y))
(declare-fun a () (Tuple Int Int))
(assert (set.member a x))
(declare-fun e () (Tuple Int Int))
(assert (= e (tuple 4 3)))
(assert (= r (rel.join x y)))
(assert (= r2 (rel.product w z)))
(assert (not (set.member e r)))
(assert (not (= r r2)))
(check-sat)