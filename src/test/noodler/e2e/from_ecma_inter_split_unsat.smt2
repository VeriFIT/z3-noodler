; A membership in a re.inter of re.from_ecma2020 regexes is split into the conjunction of the memberships
; (issue #522), so x would have to be both "a" and a nonempty sequence of b's.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x (re.inter (re.from_ecma2020 "a") (re.from_ecma2020 "b+"))))

(check-sat)
