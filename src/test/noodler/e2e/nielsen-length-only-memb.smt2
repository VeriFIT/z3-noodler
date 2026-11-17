; Cyclic equation with a length constraint: |x| >= 2 is turned into the membership
; x in re.allchar{2,}, which constrains only the length of x. Nielsen handles such memberships
; as length constraints (previously, the membership prevented using Nielsen and the
; stabilization procedure did not terminate).
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-const x String)
(assert (= (str.++ "a" x) (str.++ x "b")))
(assert (>= (str.len x) 2))
(check-sat)
