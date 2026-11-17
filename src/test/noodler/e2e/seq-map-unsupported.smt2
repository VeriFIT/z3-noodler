; seq.map is not supported by Noodler, the result must be unknown (not a wrong answer).
(set-info :smt-lib-version 2.6)
(set-info :status unknown)
(declare-const s (Seq Int))
(assert (= (seq.map (lambda ((x Int)) (+ x 1)) s) (seq.unit 3)))
(check-sat)
