; A membership in a re.union of re.from_ecma2020 regexes is split into the disjunction of the memberships
; (issue #522). Here x = "b".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.union (re.from_ecma2020 "a") (re.from_ecma2020 "b"))))
(assert (not (= x "a")))

(check-sat)
