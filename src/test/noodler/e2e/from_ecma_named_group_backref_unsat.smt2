; A named group referenced by \k<n> stays capturing (issue #474), so \k<n> must match "a".
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^(?<n>a)\k<n>$")))

(check-sat)
