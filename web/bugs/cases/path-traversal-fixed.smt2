; A sound filter: delete every ".." (not just "../").
;
;   name = name.replace("..", "")
;
; A run of n dots becomes n mod 2 dots, so no ".." can be glued together.
; Can the cleaned name still contain ".."?  (unsat = the filter is sound)
(set-logic QF_SLIA)
(declare-const name String)
(assert (str.contains (str.replace_all name ".." "") ".."))
(check-sat)
