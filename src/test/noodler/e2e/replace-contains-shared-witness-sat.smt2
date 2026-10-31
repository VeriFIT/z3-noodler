(set-logic QF_SLIA)
(set-info :status sat)
; Noetzli str-pred-small-rw_330: str.replace and str.contains of (x, y) share one decomposition of x
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (= y (str.replace x y "A")) (= x (str.replace "A" x y)))))
(check-sat)
