; https://github.com/VeriFIT/z3-noodler/issues/424
; (Seq String) is a "non-String" sequence sort (its element sort is itself
; String), so it must also fall back to Z3's built-in sequence theory instead
; of being routed to noodler (which only understands String/Seq Char).
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq String))
(declare-const x String)
(assert (= (seq.len s) 1))
(assert (= (seq.unit x) s))
(assert (= x "abc"))
(check-sat)
