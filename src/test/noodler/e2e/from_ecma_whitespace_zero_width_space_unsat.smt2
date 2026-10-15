; U+200B ZERO WIDTH SPACE right after the Zs range U+2000-U+200A is not in Zs, so it is not in \s (issue #453).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "\u{200b}"))
(assert (str.in_re x (re.from_ecma2020 "^\s$")))

(check-sat)
