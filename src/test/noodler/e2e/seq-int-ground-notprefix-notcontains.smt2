; Generic sequences (Seq Int): negated prefixof/contains with a ground sequence are handled
; by enumerating its prefixes/subsequences (as for string literals).
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
(assert (not (seq.prefixof z (seq.++ (seq.unit 1) (seq.unit 7)))))
(assert (not (seq.contains (seq.++ (seq.unit 1) (seq.unit 7)) (seq.++ x (seq.unit 1)))))
(assert (= (seq.++ x y) (seq.++ (seq.unit 0) z (seq.unit 1))))
(check-sat)
