; https://github.com/VeriFIT/z3-noodler/issues/424
; theory_str_noodler only supports the String sort. A generic (non-String)
; sequence sort such as (Seq Int) must fall back to Z3's built-in sequence
; theory, not be silently mishandled and returned as unknown.
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-const s (Seq Int))
(assert (= (seq.len s) 0))
(check-sat)
