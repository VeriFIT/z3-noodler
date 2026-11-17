; seq.nth_u extensionality: x and y are equal by word equations (not by the E-graph),
; so the out-of-bounds seq.nth values must be equal.
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
; x and y are both forced to be [1] by word equations (not by the E-graph)
(assert (= (seq.++ x (seq.unit 1)) (seq.++ (seq.unit 1) x)))
(assert (= (seq.++ y (seq.unit 1)) (seq.++ (seq.unit 1) y)))
(assert (= (seq.len x) 1))
(assert (= (seq.len y) 1))
(assert (= (seq.nth x 5) 0))
(assert (= (seq.nth y 5) 2))
(check-sat)
