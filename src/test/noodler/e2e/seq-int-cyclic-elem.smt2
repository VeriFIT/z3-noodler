; Generic sequences (Seq Int): cyclic (quadratic) equation solved by Nielsen; sat only if a = b.
; The membership x in re.allchar{2,} derived from |x| >= 2 constrains only the length of x,
; so Nielsen can still be used (it handles it as a length constraint).
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x (Seq Int))
(declare-const a Int)
(declare-const b Int)
(assert (= (seq.++ (seq.unit a) x) (seq.++ x (seq.unit b))))
(assert (>= (seq.len x) 2))
(assert (or (< a 0) (> a 5)))
(assert (<= 0 b 10))
(check-sat)
