; U+1680 OGHAM SPACE MARK is whitespace, so it is not in [^\s] (issue #453).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "\u{1680}"))
(assert (str.in_re x (re.from_ecma2020 "^[^\s]$")))

(check-sat)
