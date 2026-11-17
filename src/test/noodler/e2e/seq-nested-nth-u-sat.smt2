; nested sequences: seq.nth of (Seq (Seq Int)) is a sequence term (replaced by a fresh variable),
; out-of-bounds values must be consistent with the values of x and y.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x (Seq (Seq Int)))
(declare-const y (Seq (Seq Int)))
(declare-const a Int)
(assert (= (seq.nth x 3) (seq.unit 0)))
(assert (= (seq.nth y 3) (seq.unit a)))
(assert (not (= a 0)))
(assert (= (seq.len x) (seq.len y)))
(check-sat)
