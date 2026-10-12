; One iteration "a" followed by \1 = "a". A second, empty iteration would fail (ES2020 RepeatMatcher, step 2.b).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "aa"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(a)|){0,2}\1$")))

(check-sat)
