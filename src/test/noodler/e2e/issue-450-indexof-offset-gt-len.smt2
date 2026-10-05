; Issue #450 variant: offset > |s| gives -1 (sat). Used to loop in loop protection, as the blocking
; lemma built from the unsat core of the length check was rewritten to true.
(set-logic ALL)
(set-info :status sat)
(declare-const s String)
(declare-const t String)
(assert (str.in_re s (re.++ re.allchar re.allchar)))
(assert (= (str.len t) 0))
(assert (not (= (str.indexof s t 3) 3)))
(check-sat)
