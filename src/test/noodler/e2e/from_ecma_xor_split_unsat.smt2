; A membership in a re.xor of re.from_ecma2020 regexes is split into the exclusive disjunction of the memberships
; (issue #522). The string "a" matches both patterns, so it is not in their exclusive disjunction.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x (re.xor (re.from_ecma2020 "a") (re.from_ecma2020 "a|b"))))
(assert (= x "a"))

(check-sat)
