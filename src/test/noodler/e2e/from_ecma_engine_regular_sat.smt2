; Under the engine semantics, a regular pattern only has to match a substring of x,
; e.g. x = "ac" (issue #495, the result used to be unknown).
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "a")))
(assert (str.suffixof "c" x))

(check-sat)
