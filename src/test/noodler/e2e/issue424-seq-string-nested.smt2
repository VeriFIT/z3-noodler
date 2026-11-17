; https://github.com/VeriFIT/z3-noodler/issues/424
; Sequences nested over String, i.e., (Seq String). The formula is sat (e.g., s = ("a" "b")).
; Z3's built-in theory_seq returns unknown here (it gives up while relating seq.nth_i
; indirections once the length reaches 2). Noodler handles (Seq String) as a generic
; sequence whose elements (strings) are abstracted by symbols.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq String))
(assert (= (seq.len s) 2))
(check-sat)
