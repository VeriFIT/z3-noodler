; A lookahead inside a lookbehind sees the rest of the whole string (issue #472).
; The lookahead at position 0 requires "b", but x starts with "a".
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^a(?<=(?=b)a)b$")))

(check-sat)
