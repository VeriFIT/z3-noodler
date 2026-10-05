; Issue #450 variant: indexof(s, "", |s|) cannot be -1.
(set-logic ALL)
(set-info :status unsat)
(declare-const s String)
(declare-const t String)
(assert (str.in_re s (re.++ re.allchar re.allchar)))
(assert (= (str.len t) 0))
(assert (= (str.indexof s t 2) (- 1)))
(check-sat)
