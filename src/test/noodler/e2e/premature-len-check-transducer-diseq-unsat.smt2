; Premature length checks prune the noodles of the transducer although the formula has postponed disequations.
; Each occurrence of "ab" replaced shortens x and x contains one right after u, so |y| = |x| is unsat.
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun u () String)
(declare-fun v () String)
(assert (= y (str.replace_all x "ab" "c")))
(assert (= x (str.++ u "a" v)))
(assert (not (= u v)))
(assert (= (str.len y) (str.len x)))
(assert (str.in_re v (re.+ (str.to_re "b"))))
(check-sat)
