; https://github.com/VeriFIT/z3-noodler/issues/445
; ReplaceAllPrefixTree::add_find allowed an inner replace_all with an empty
; replacement ("a" -> "") to be combined with a later replace_all whose find
; has length >= 2 ("bc" -> "d"). Deleting text can join neighbouring
; characters and create a new occurrence of the later find, which the
; simultaneous-matching construction cannot detect, wrongly making this unsat.
; Expected sat, e.g. y = "bac": "bac" -> "bc" -> "d".
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const y String)
(assert (str.prefixof "ba" y))
(assert (= (str.replace_all (str.replace_all y "a" "") "bc" "d") "d"))
(check-sat)
