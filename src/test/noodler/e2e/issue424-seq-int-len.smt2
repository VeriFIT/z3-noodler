; https://github.com/VeriFIT/z3-noodler/issues/424
; A generic (non-String) sequence sort such as (Seq Int) is handled by Noodler
; (stabilization procedure), it must not be silently mishandled and returned as unknown.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq Int))
(assert (= (seq.len s) 0))
(check-sat)
