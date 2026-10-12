; A backreference inside a lookbehind nested in its own group matches the empty string (issue #476), because the
; group is still open at the lookbehind position.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "a"))
(assert (str.in_re x (re.from_ecma2020 "^(a(?<=a\1))$")))

(check-sat)
