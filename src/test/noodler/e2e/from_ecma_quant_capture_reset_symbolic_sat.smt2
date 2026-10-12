; Symbolic variant of from_ecma_quant_capture_reset_sat: the only string of length 2 starting with "a" that
; matches ^(?:(a)|b){2}\1$ is "ab" (the second iteration resets group 1).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "^(?:(a)|b){2}\1$")))
(assert (= (str.len x) 2))
(assert (str.prefixof "a" x))

(check-sat)
