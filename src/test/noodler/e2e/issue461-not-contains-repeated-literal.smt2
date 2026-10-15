; https://github.com/VeriFIT/z3-noodler/issues/461
; Repeated literals were dropped when replaced by handle variables, so the
; needle "y c y" was encoded as "y y", giving a wrong sat.
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (str.to_re "a"))))
(assert (str.in_re y (re.* (str.to_re "a"))))
(assert (not (str.contains (str.++ x "c" x) (str.++ y "c" y))))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(check-sat)
