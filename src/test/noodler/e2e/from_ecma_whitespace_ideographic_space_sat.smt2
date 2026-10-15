; \s contains every Unicode Zs character (issue #453), e.g. U+3000 IDEOGRAPHIC SPACE.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{3000}"))
(assert (str.in_re x (re.from_ecma2020 "^\s$")))

(check-sat)
