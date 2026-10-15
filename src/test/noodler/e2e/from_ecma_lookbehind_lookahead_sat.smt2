; A lookahead inside a lookbehind sees the rest of the whole string, not only the lookbehind target (issue #472).
; The lookbehind at position 1 matches "a" before it and its lookahead at position 0 sees "ab".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^a(?<=(?=ab)a)b$")))

(check-sat)
