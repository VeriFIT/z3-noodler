; https://github.com/VeriFIT/z3-noodler/issues/449
; Finite-needle not-contains heuristic: pruned haystack automata must keep initial/final states.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const x String)
(declare-const t String)
(assert (str.in_re t (re.union (str.to_re "a") (str.to_re "b"))))
(assert (not (str.contains x t)))
(assert (= (str.len x) 3))
(check-sat)
