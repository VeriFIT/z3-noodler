; x = "aaaa" must match (a*b*)\1, so asserting the negation is unsatisfiable.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "aaaa"))
(assert (not (str.in_re x (re.from_ecma2020 "(a*b*)\1"))))

(check-sat)
