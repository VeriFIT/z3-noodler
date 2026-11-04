; issue #502: the NFA of a bounded loop had a quadratic number of transitions in the upper bound
(set-info :status sat)
(set-logic QF_SLIA)
(declare-const x String)
(assert (str.in_re x ((_ re.loop 0 800) (re.range "a" "z"))))
(assert (str.in_re x (re.++ re.all (str.to_re "q") re.all)))
(assert (> (str.len x) 5))
(check-sat)
