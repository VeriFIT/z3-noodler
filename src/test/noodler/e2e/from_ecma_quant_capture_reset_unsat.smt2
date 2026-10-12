; Captures inside a quantified atom are reset at the start of every iteration (ES2020 RepeatMatcher, step 4).
; The second iteration takes "b", so \1 cannot match the "a" captured in the first iteration.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "aba"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(a)|b){2}\1$")))

(check-sat)
