; https://github.com/VeriFIT/z3-noodler/issues/424
; Regression check that (Seq String) is correctly dispatched away from
; noodler to Z3's built-in sequence theory (confirmed sat/unknown, never a
; crash or a bogus "mangled into a fresh string var" answer).
;
; This particular formula is actually sat (s = ("a" "b")), but Z3's built-in
; theory_seq is known-incomplete for sequences nested over String (it gives
; up while relating seq.nth_i indirections once the length reaches 2), and
; returns "unknown" ("(seq.giveup ... is unsolved)" in the trace). That is a
; pre-existing Z3 core (theory_seq) limitation, unrelated to noodler and to
; the family-id dispatch fix for issue 424 -- it reproduces identically with
; smt.string_solver=seq (noodler not involved at all). Not something we can
; or should fix here; this test documents the current, honest behavior.
(set-info :smt-lib-version 2.6)
(set-info :status unknown)
(declare-const s (Seq String))
(assert (= (seq.len s) 2))
(check-sat)
