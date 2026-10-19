; Under the engine semantics, a regular pattern describes the strings containing a match (issue #521).
; The strings containing "a" are exactly the strings containing a nonempty sequence of a's.
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(assert (= (re.from_ecma2020 "a") (re.from_ecma2020 "a+")))

(check-sat)
