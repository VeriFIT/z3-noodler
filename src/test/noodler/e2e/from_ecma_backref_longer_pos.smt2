; Positive form with a longer backreference pattern.
; Pattern (a*b)\1 introduces a fresh group variable for "a*b", then backreferences it.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "(a*b)\1")))

(check-sat)
(get-model)
