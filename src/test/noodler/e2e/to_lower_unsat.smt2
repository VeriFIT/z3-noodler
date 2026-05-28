(set-logic QF_SLIA)
(set-info :status unsat)

(declare-const zz String)
(assert (= (str.to_lower zz) "AAAMMMZZZ"))
(assert (str.in_re zz (re.++ (re.* (str.to_re "A")) (re.* (str.to_re "M")) (re.* (str.to_re "Z")))))

(check-sat)
