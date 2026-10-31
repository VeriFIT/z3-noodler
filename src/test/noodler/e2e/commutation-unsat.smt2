(set-logic QF_SLIA)
(set-info :status unsat)
; Noetzli str-term-small-rw_954: "A" x = x v forces x in A* and v = "A"
(declare-fun x () String)
(assert (not (= (str.replace (str.++ "A" x) x "") "A")))
(check-sat)
