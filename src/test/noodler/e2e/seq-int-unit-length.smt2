; Generic sequences (Seq Int): Z3 must know that |seq.unit b| = 1 (as for string
; literals), otherwise its length assignment contradicts the length constraints of
; the decision procedure and loop protection keeps blocking the same assignment.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
(declare-const b Int)
(assert (seq.suffixof (seq.++ x y) (seq.++ (seq.unit b) y)))
(assert (= y x))
(assert (>= (seq.len z) 2))
(check-sat)
