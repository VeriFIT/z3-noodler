; A word boundary inside a lookbehind sees the rest of the whole string (issue #472).
; Between "a" and "b" there is no word boundary.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^a(?<=a\b)b$")))

(check-sat)
