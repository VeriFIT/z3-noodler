; The disjunction of memberships is not merged into a re.union (issue #522), so x is "a" or "b"
; and it cannot have length 2.
(set-logic QF_SLIA)
(set-info :status unsat)

(declare-const x String)

(assert (or (str.in_re x (re.from_ecma2020 "a")) (str.in_re x (re.from_ecma2020 "b"))))
(assert (= (str.len x) 2))

(check-sat)
