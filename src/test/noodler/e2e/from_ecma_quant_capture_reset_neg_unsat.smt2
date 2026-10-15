; Negation of from_ecma_quant_capture_reset_sat: "ab" matches ^(?:(a)|b){2}\1$, so it cannot be outside of it.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "ab"))
(assert (not (str.in_re x (re.from_ecma2020 "^(?:(a)|b){2}\1$"))))

(check-sat)
