; Issue #450: wrong SAT without model generation for indexof(s, t, |s|) with |t| = 0.
; The negated arithmetic literals (e.g., not(|s| >= 2)) were dropped from the context of the length check.
(set-logic ALL)
(set-info :status unsat)
(declare-const s String)
(declare-const t String)
(assert (str.in_re s (re.++ re.allchar re.allchar)))
(assert (= (str.len t) 0))
(assert (not (= (str.indexof s t 2) 2)))
(check-sat)
