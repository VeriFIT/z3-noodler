; The memberships of a negated conjunction must not be merged into one negated membership in a re.inter
; (issue #522). Of the strings in a|b, only x = "b" does not match both patterns.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (not (and (str.in_re x (re.from_ecma2020 "a")) (str.in_re x (re.from_ecma2020 "a|b")))))
(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "b"))))

(check-sat)
