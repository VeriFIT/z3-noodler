; '.*' matches every string without a line terminator (issue #454), e.g. one with VT.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "^a.*b$")))
(assert (str.contains x "\u{b}"))

(check-sat)
