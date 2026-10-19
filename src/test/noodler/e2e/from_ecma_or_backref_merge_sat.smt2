; Memberships in a non-regular pattern must not be merged with other memberships of the same string
; into a re.union either (issue #522). For example, x = "aa" or x = "b".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (or (str.in_re x (re.from_ecma2020 "(a)\1")) (str.in_re x (re.from_ecma2020 "b"))))

(check-sat)
