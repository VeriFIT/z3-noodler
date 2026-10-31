(set-logic QF_SLIA)
(set-info :status sat)
; x "aa" = v x forces x in a* and v = "aa"
(declare-fun x () String)
(declare-fun v () String)
(assert (= (str.++ x "aa") (str.++ v x)))
(assert (> (str.len x) 2))
(check-sat)
