; VT is not a line terminator, so '.' matches it (issue #454).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{b}"))
(assert (str.in_re x (re.from_ecma2020 "^.$")))

(check-sat)
