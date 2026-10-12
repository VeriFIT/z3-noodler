; A backreference inside a lookahead refers to the captures at the lookahead position (issue #457).
; Group 1 is still undefined at the lookahead, so \1 matches "" and the lookahead requires "b" at position 0.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^(?=\1b)(a)b$")))

(check-sat)
