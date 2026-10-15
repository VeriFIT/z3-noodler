; U+3000 IDEOGRAPHIC SPACE is whitespace, so it is not in \S (issue #453).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "\u{3000}"))
(assert (str.in_re x (re.from_ecma2020 "^\S$")))

(check-sat)
