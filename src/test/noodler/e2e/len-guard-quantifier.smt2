; The length formula of the first solution is passed to the main context guarded by a fresh literal;
; the quantifier (not visible to the length check) rejects some lengths of x.
(set-info :status sat)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun f (Int) Bool)
(assert (= (str.++ x y) "abcab"))
(assert (forall ((i Int)) (! (=> (f i) (>= i 3)) :pattern ((f i)))))
(assert (f (str.len x)))
(check-sat)
