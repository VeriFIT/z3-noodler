; A regular pattern is compared with an ordinary regex as a classical regex (issue #521). Both describe {a, b},
; so the disequation does not hold.
(set-logic QF_S)
(set-info :status unsat)

(assert (not (= (re.from_ecma2020 "[ab]") (re.union (str.to_re "a") (str.to_re "b")))))

(check-sat)
