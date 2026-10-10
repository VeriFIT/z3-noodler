; https://github.com/VeriFIT/z3-noodler/issues/440
; The haystack automaton keeps a dead a.x branch from the intersection; x and ax are not factors of abc.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-fun h () String)
(declare-fun n () String)
(assert (str.in_re h (re.inter (re.union (str.to_re "abc") (str.to_re "axd"))
                               (re.union (str.to_re "abc") (str.to_re "axe")))))
(assert (str.in_re n (re.union (str.to_re "x") (str.to_re "ax"))))
(assert (not (str.contains h n)))
(check-sat)
