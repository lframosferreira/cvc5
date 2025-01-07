; SMT-LIB2 instance for Frobenius Coin Problem with consecutive primes 17 and 19

(set-logic LIA)

; Declare variables for the coefficients of the coins (x and y)
(declare-const x Int)
(declare-const y Int)

; Declare variable for the target amount (t)
(declare-const t Int)

; Constraints: x and y must be non-negative integers
(assert (>= x 0))
(assert (>= y 0))

; Equation: t = 17 * x + 19 * y
(assert (= t (+ (* 17 x) (* 19 y))))

; Declare the Frobenius number (f), the largest t that cannot be expressed
(declare-const f Int)

; f must be less than 17 * 19 (product of the primes, which bounds the solution space)
(assert (< f (* 17 19)))

; f cannot be expressed as 17 * x + 19 * y for any non-negative x and y
(assert (not (exists ((x Int) (y Int))
              (and (>= x 0) (>= y 0) (= f (+ (* 17 x) (* 19 y)))))))

; f + 1 can be expressed as 17 * x + 19 * y
(assert (exists ((x Int) (y Int))
              (and (>= x 0) (>= y 0) (= (+ f 1) (+ (* 17 x) (* 19 y))))))

; Check satisfiability
(check-sat)

; Get the value of f if satisfiable
(get-value (f))

