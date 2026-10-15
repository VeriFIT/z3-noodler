; Without the dotAll flag, '.' does not match a line terminator (issue #454), e.g. CR or U+2029 PARAGRAPH SEPARATOR.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (or (= x "\u{d}") (= x "\u{2029}")))
(assert (str.in_re x (re.from_ecma2020 "^.$")))

(check-sat)
