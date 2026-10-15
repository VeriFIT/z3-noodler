; Negation of from_ecma_own_group_backref_sat: "a" matches ^(a\1)$, so it cannot be outside of it.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "a"))
(assert (not (str.in_re x (re.from_ecma2020 "^(a\1)$"))))

(check-sat)
