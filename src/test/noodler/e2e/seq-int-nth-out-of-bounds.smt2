; Generic sequences (Seq Int): seq.nth outside of the bounds is the uninterpreted seq.nth_u.
; Its interpretation must be included in the model, otherwise the value of b (eliminated
; by preprocessing as b = (seq.nth y 0)) is evaluated with a default value violating b != 0.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const y (Seq Int))
(declare-const b Int)
(assert (= (seq.nth y 0) b))
(assert (distinct 0 b))
(assert (= (seq.len y) 0))
(check-sat)
