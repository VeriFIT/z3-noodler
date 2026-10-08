; https://github.com/VeriFIT/z3-noodler/issues/444
; ReplaceAllPrefixTree::add_find left stale entries in
; one_symbol_replace_to_prefix_state when a single-character find's state was
; later turned final by another single-character find, causing the combined
; transducer for the outer replace_all to incorrectly attach to a state whose
; output had already been overwritten by the inner replacement. After
; replace_all(y, "a", "d"), no "a" survives, so the outer replace_all(_, "ab",
; "c") is the identity, and the result can only be "c" when y = "c", which
; contradicts "not (str.contains y "c")".
(set-logic QF_SLIA)
(set-info :status unsat)
(declare-const y String)
(assert (= (str.replace_all (str.replace_all y "a" "d") "ab" "c") "c"))
(assert (not (str.contains y "c")))
(check-sat)
