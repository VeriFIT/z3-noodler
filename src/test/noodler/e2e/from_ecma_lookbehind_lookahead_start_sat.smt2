; A lookahead inside a lookbehind at position 0 sees the whole string "a" (issue #472).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "a"))
(assert (str.in_re x (re.from_ecma2020 "^(?<=(?=a))a$")))

(check-sat)
