; Regular patterns in a language disequation are compared as classical regexes (issue #521), {a} and {b} differ.
(set-logic QF_S)
(set-info :status sat)

(assert (not (= (re.from_ecma2020 "a") (re.from_ecma2020 "b"))))

(check-sat)
