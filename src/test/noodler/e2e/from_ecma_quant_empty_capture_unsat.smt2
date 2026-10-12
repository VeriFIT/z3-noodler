; An iteration beyond the quantifier minimum fails if it matches the empty string (ES2020 RepeatMatcher, step 2.b).
; Without this check, the iterations "a" and "" would set group 1 to "" and \1 would match the empty string.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "a"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(a?)){0,2}\1$")))

(check-sat)
