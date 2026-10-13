; \s contains the Zs range U+2000-U+200A (issue #453), also inside a character class.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{2005}"))
(assert (str.in_re x (re.from_ecma2020 "^[\s]$")))

(check-sat)
