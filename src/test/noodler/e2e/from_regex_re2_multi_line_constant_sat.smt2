; The second line of x starts with a. A positive membership adds no quantifier, otherwise the model check of the
; quantifier instantiation fails on the lengths of the fresh variables that the string solver did not need.
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex re2) "(?m)^a")))
(assert (= x "b\u{a}a"))

(check-sat)
