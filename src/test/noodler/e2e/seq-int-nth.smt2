; Generic sequences (Seq Int) with seq.nth.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq Int))
(assert (= (seq.len s) 3))
(assert (= (seq.nth s 2) 7))
(assert (= (seq.nth s 0) (+ (seq.nth s 2) 1)))
(assert (= (seq.nth s 1) (seq.nth s 0)))
(check-sat)
