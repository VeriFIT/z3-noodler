; https://github.com/VeriFIT/z3-noodler/issues/449
; x contains both letters, so it contains every possible value of t.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-const x String)
(declare-const t String)
(assert (str.in_re x (re.* (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re t (re.union (str.to_re "a") (str.to_re "b"))))
(assert (not (str.contains x t)))
(assert (str.in_re x (re.++ re.all (str.to_re "a") re.all (str.to_re "b") re.all)))
(check-sat)
