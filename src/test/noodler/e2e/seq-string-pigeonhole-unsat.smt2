; (Seq String): three pairwise distinct elements, each of them "a" or "b".
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const s (Seq String))
(assert (= (seq.len s) 3))
(assert (forall ((i Int)) (=> (and (<= 0 i) (< i 3)) (or (= (seq.nth s i) "a") (= (seq.nth s i) "b")))))
(assert (distinct (seq.nth s 0) (seq.nth s 1) (seq.nth s 2)))
(check-sat)
