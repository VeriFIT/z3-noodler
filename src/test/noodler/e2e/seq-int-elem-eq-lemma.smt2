; Generic sequences (Seq Int): the formula is sat only if a != b.
; Noodler forces Z3 to decide the equality of the elements a and b (it tries a = b first).
; Under a = b, the string part is unsat; the learned lemma must contain the element
; equality a = b, otherwise the sat branch a != b would be blocked as well.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq Int))
(declare-const a Int)
(declare-const b Int)
(assert (seq.prefixof (seq.unit b) s))
(assert (not (seq.contains s (seq.unit a))))
(assert (> a 10))
(assert (> b 10))
(assert (>= (seq.len s) 2))
(check-sat)
