; A conjunction nested in a disjunction is not split into separate assertions, so its memberships of the same
; string must not be merged into one membership in a re.inter (issue #522). Here x = "a".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)
(declare-const p Bool)

(assert (or (and (str.in_re x (re.from_ecma2020 "a")) (str.in_re x (re.from_ecma2020 "a|b"))) p))
(assert (not p))

(check-sat)
