; An unreferenced named group is non-capturing, so it stays regular under a Kleene plus (issue #474).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(?<n>a)|b)+$")))

(check-sat)
