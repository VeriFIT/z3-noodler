(set-logic QF_SLIA)
(set-info :status unsat)

(declare-const x String)

(assert (>= (str.to_int x) 0))
(assert (str.in_re x (re.++ (re.+ (str.to_re "82")) (str.to_re "804"))))
(assert (< (* 5 (str.to_int x)) 26))
(assert (< (+ (* 10 (str.len x)) (* (- 7) (str.to_int x))) 44))

(check-sat)
