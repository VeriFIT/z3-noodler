; Without the dotAll flag, '.' does not match a line terminator (issue #454), e.g. LF.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "a\u{a}b"))
(assert (str.in_re x (re.from_ecma2020 "^a.b$")))

(check-sat)
