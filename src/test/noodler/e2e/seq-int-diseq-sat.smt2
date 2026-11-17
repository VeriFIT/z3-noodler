; Generic sequences (Seq Int): sequences without any element terms; distinct values
; must be chosen for them in the model.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
(assert (= (seq.len x) 1))
(assert (= (seq.len y) 1))
(assert (= (seq.len z) 1))
(assert (distinct x y z))
(assert (= (seq.++ x y) (seq.++ x (seq.unit 3))))
(check-sat)
