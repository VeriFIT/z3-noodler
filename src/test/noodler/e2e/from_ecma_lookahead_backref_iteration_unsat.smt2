; A backreference inside a lookahead refers to the capture of the current iteration, not of the last one (issue #457).
; In the first iteration \1 = "a", but the next character is "b".
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "abb"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(\w)(?=\1)){2}\w$")))

(check-sat)
