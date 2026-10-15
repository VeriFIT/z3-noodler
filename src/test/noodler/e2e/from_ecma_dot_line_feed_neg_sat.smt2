; Without the dotAll flag, '.' does not match a line terminator (issue #454), so LF is outside of ^.$.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{a}"))
(assert (not (str.in_re x (re.from_ecma2020 "^.$"))))

(check-sat)
