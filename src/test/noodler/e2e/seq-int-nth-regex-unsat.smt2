; Generic sequences (Seq Int): axioms of seq.nth must be added on the base level (as for other
; string functions), otherwise they are lost after backtracking (found by differential fuzzing).
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const x (Seq Int))
(declare-const y (Seq Int))
(declare-const z (Seq Int))
(declare-const a Int)
(declare-const b Int)
(assert (seq.in.re y (re.++ (seq.to.re (seq.unit 2)) (re.* (as re.allchar (RegEx (Seq Int)))))))
(assert (seq.in.re x (re.comp (re.++ (as re.all (RegEx (Seq Int))) (seq.to.re (seq.unit 1)) (as re.all (RegEx (Seq Int)))))))
(assert (= (seq.nth x 0) a))
(assert (= (seq.nth y 0) 0))
(check-sat)
