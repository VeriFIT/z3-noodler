; A named group referenced by \k<n> stays capturing (issue #474).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "aa"))
(assert (str.in_re x (re.from_ecma2020 "^(?<n>a)\k<n>$")))

(check-sat)
