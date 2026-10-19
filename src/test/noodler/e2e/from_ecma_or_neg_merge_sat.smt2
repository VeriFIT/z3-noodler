; Negated memberships of the same string in a disjunction must not be merged into one membership in
; (re.union (re.comp (re.from_ecma2020 "a")) (re.comp (re.from_ecma2020 "b"))) (issue #522).
; For example, x = "a".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (or (not (str.in_re x (re.from_ecma2020 "a"))) (not (str.in_re x (re.from_ecma2020 "b")))))

(check-sat)
