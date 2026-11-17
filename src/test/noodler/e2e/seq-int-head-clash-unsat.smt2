; Generic sequences (Seq Int) solved by Noodler: the first elements of both sides
; must be equal, which contradicts a != b.
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const s (Seq Int))
(declare-const t (Seq Int))
(declare-const a Int)
(declare-const b Int)
(assert (= (seq.++ (seq.unit a) s) (seq.++ (seq.unit b) t)))
(assert (not (= a b)))
(check-sat)
