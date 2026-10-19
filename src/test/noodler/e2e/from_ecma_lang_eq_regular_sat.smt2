; Regular patterns in a language equation are compared as classical regexes (issue #521). Both describe {a, b}.
(set-logic QF_S)
(set-info :status sat)

(assert (= (re.from_ecma2020 "a|b") (re.from_ecma2020 "[ab]")))

(check-sat)
