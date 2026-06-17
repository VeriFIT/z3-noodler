(set-logic QF_SLIA)
(set-info :status unsat)

(declare-const x String)
(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))
(assert (= (= x "a") (= x "b")))

(check-sat)
