(set-logic QF_SLIA)
(set-info :status unsat)
; Noetzli str-pred-small-rw_165: str.replace and str.contains of (x, y) share one decomposition of x
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.suffixof x (str.replace x y "")) (= x (str.replace x y "")))))
(check-sat)
