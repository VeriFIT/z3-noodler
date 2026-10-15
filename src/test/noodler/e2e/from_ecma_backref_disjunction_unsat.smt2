; The membership under the disjunction becomes relevant only above the base level, so its axioms are deleted and
; added again when backtracking. b1 implies n = 5, which is excluded, so x must match both aab and bba.
(set-logic QF_SLIA)
(set-info :status unsat)

(declare-const x String)
(declare-const b1 Bool)
(declare-const n Int)

(assert (or b1 (str.in_re x (re.from_ecma2020 "^(a)\1b$"))))
(assert (or (not b1) (= n 5)))
(assert (or (> n 7) (< n 2)))
(assert (str.in_re x (re.from_ecma2020 "^(b)\1a$")))

(check-sat)
