; Generic sequences (Seq Int) with regular constraints.
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const s (Seq Int))
(assert (seq.in.re s (re.* (re.union (seq.to.re (seq.unit 1)) (seq.to.re (seq.unit 2))))))
(assert (seq.contains s (seq.unit 3)))
(check-sat)
