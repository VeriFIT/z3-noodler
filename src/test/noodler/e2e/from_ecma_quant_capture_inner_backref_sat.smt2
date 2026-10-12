; A backreference inside the quantified atom refers to the capture of the current iteration.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "aaaa"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(a)\1){2}$")))

(check-sat)
