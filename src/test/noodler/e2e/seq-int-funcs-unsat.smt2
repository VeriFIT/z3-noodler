; Generic sequences (Seq Int) with extended functions.
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const s (Seq Int))
(declare-const a Int)
(assert (seq.prefixof (seq.unit a) s))
(assert (not (seq.contains s (seq.unit a))))
(check-sat)
