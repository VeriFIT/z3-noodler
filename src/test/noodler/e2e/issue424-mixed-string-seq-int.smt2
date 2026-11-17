; https://github.com/VeriFIT/z3-noodler/issues/424
; A formula mixing plain String constraints with a generic (non-String)
; sequence sort. Since only one theory can handle the whole "seq" family per
; context, Noodler handles both the String part and the (Seq Int) part
; (generic sequences are solved by the stabilization procedure).
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const x String)
(declare-const y String)
(declare-const s (Seq Int))
(assert (= x y))
(assert (= x "abc"))
(assert (= (seq.len s) 5))
(check-sat)
