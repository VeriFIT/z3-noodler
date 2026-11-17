; https://github.com/VeriFIT/z3-noodler/issues/424
; With smt.str.noodler_seq=false, generic (non-String) sequence sorts make the
; whole seq family (Strings included) fall back to Z3's built-in theory_seq.
(set-option :smt.str.noodler_seq false)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x String)
(declare-const s (Seq Int))
(assert (= x "abc"))
(assert (= (seq.len s) 5))
(assert (= (seq.nth s 0) 42))
(check-sat)
