; x = "abab" must match (ab)\1, so asserting the negation is unsatisfiable.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "abab"))
(assert (not (str.in_re x (re.from_ecma2020 "(ab)\1"))))

(check-sat)
