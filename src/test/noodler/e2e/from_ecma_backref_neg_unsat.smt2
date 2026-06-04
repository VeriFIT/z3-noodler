; Negation of from_ecma2020 contradicts a ground assignment.
; x = "aa" must match (a)\1 (the fresh group variable is "a", backreference is "a"),
; so asserting x does NOT match is unsatisfiable.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "aa"))
(assert (not (str.in_re x (re.from_ecma2020 "(a)\1"))))

(check-sat)
