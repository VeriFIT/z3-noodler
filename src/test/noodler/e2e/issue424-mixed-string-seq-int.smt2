; https://github.com/VeriFIT/z3-noodler/issues/424
; A formula mixing plain String constraints with a generic (non-String)
; sequence sort must still be solved correctly: since only one theory can
; handle the whole "seq" family per context, the presence of (Seq Int) must
; make the whole family (Strings included) fall back to Z3's built-in
; sequence theory rather than leaving the String part to noodler and the
; (Seq Int) part unhandled.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x String)
(declare-const y String)
(declare-const s (Seq Int))
(assert (= x y))
(assert (= x "abc"))
(assert (= (seq.len s) 5))
(check-sat)
