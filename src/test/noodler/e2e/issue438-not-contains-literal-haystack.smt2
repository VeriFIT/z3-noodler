; https://github.com/VeriFIT/z3-noodler/issues/438
; Literal in the haystack.
; The |needle| > |haystack| fallback must count literal lengths (it used to use
; unconstrained literal handles, giving a wrong sat). The fallback is only an
; underapproximation, so noodler answers unknown; the correct answer is unsat.
(set-logic QF_SLIA)
; (set-info :status unknown)
(set-info :status unsat)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.* (re.union (str.to_re "a") (str.to_re "b")))))
(assert (str.in_re y (re.* (str.to_re "ab"))))
(assert (not (str.contains (str.++ "ab" x) y)))
(assert (= (str.len y) 2))
(check-sat)
