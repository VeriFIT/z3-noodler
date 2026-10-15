; Captures inside a quantified atom are reset at the start of every iteration (ES2020 RepeatMatcher, step 4).
; The second iteration takes "b", so group 1 is undefined again and \1 matches the empty string.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(a)|b){2}\1$")))

(check-sat)
