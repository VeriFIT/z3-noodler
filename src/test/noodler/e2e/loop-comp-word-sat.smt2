; issue #466: (loop (comp (to_re w)) n m) with |w| >= 2 crashed the rewriter
(set-logic QF_S)
(set-info :status sat)
(declare-const x String)
(assert (str.in_re x ((_ re.loop 2 3) (re.comp (str.to_re "ab")))))
(check-sat)
