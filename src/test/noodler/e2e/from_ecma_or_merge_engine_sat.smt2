; Under the engine semantics, memberships of the same string in a disjunction must not be merged into
; a re.union either (issue #522). For example, x = "aa" or x = "b".
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (or (str.in_re x (re.from_ecma2020 "(a)\1")) (str.in_re x (re.from_ecma2020 "b"))))

(check-sat)
