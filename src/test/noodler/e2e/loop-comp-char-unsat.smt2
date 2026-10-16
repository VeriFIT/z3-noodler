; issue #466: (loop (comp (to_re c)) n m) = comp (to_re c) for a single character c
(set-logic QF_S)
(set-info :status unsat)
(declare-const x String)
(assert (= x "a"))
(assert (str.in_re x ((_ re.loop 2 3) (re.comp (str.to_re "a")))))
(check-sat)
