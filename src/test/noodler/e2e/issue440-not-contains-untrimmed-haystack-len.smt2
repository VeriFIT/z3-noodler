; https://github.com/VeriFIT/z3-noodler/issues/440
; x = bb (its automaton keeps a dead a-branch), y = a, z = b.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "bb"))))
(assert (str.in_re y (re.union (str.to_re "a") (str.to_re "b"))))
(assert (str.in_re z (str.to_re "b")))
(assert (not (str.contains x y)))
(assert (not (str.contains y z)))
(assert (= (str.len x) 2))
(check-sat)
