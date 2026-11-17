; Generic sequences (Seq Int) with seq.nth.
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const s (Seq Int))
(declare-const t (Seq Int))
(assert (= s (seq.++ (seq.unit 1) t)))
(assert (= (seq.nth s 0) 2))
(check-sat)
