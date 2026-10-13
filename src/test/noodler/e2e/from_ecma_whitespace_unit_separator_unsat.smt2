; U+001F UNIT SEPARATOR is not whitespace (issue #453).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "\u{1f}"))
(assert (str.in_re x (re.from_ecma2020 "^\s$")))

(check-sat)
