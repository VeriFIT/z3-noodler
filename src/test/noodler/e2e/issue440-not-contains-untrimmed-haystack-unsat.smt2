; https://github.com/VeriFIT/z3-noodler/issues/440
; Every needle value is a real factor of abc.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun h () String)
(declare-fun n () String)
(assert (str.in_re h (re.inter (re.union (str.to_re "abc") (str.to_re "axd"))
                               (re.union (str.to_re "abc") (str.to_re "axe")))))
(assert (str.in_re n (re.union (str.to_re "bc") (str.to_re "ab"))))
(assert (not (str.contains h n)))
(check-sat)
