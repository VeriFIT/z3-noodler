(set-logic QF_SLIA)
(set-info :status unsat)

(declare-const zz String)
(assert (= (str.to_upper zz) "aaammmzzz"))
(assert (str.in_re zz (re.++ (re.* (str.to_re "a")) (re.* (str.to_re "m")) (re.* (str.to_re "z")))))

(check-sat)
