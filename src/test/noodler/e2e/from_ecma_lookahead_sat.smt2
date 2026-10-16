; The lookahead constrains the suffix after its position: x = "aab" matches,
; since "ab" follows the first "a".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "a(?=ab)ab")))

(check-sat)
