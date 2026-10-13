; Without the dotAll flag, '.' does not match a line terminator (issue #454), e.g. U+2028 LINE SEPARATOR.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "a\u{2028}b"))
(assert (str.in_re x (re.from_ecma2020 "^a.b$")))

(check-sat)
