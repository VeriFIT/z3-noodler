; Regular patterns nested in another regex operation are compared as classical regexes too (issue #521).
; Both sides describe {a, b}.
(set-logic QF_S)
(set-info :status sat)

(assert (= (re.union (re.from_ecma2020 "a") (re.from_ecma2020 "b")) (re.from_ecma2020 "a|b")))

(check-sat)
