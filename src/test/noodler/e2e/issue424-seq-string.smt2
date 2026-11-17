; https://github.com/VeriFIT/z3-noodler/issues/424
; (Seq String) is a "non-String" sequence sort (its element sort is itself
; String). Noodler handles it as a generic sequence whose elements (strings)
; are abstracted by symbols.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq String))
(declare-const x String)
(assert (= (seq.len s) 1))
(assert (= (seq.unit x) s))
(assert (= x "abc"))
(check-sat)
