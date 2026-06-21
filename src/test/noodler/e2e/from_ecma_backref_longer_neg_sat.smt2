; "ab" (length 2) does not match (ab)\1 (which requires length 4),
; so the negated constraint with x = "ab" is satisfiable.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "ab"))
(assert (not (str.in_re x (re.from_ecma2020 "(ab)\1"))))

(check-sat)
(get-model)
