(set-logic QF_S)

(declare-const w String)

(assert (str.in_re w (re.from_ecma2020 'a')))
(assert (= (str.len w) 1))
(check-sat)
(get-model)