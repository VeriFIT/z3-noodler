; Regular patterns in a language equation are compared as classical regexes (issue #521), so the equation of {a}
; and {b} does not hold.
(set-logic QF_S)
(set-info :status unsat)

(assert (= (re.from_ecma2020 "a") (re.from_ecma2020 "b")))

(check-sat)
