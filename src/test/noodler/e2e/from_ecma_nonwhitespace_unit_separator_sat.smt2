; U+001F UNIT SEPARATOR is not whitespace, so it is in \S (issue #453).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{1f}"))
(assert (str.in_re x (re.from_ecma2020 "^\S$")))

(check-sat)
