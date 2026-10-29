; The word foo is in the middle of x. A positive membership adds no quantifier, otherwise the model check of the
; quantifier instantiation fails on the lengths of the fresh variables that the string solver did not need.
(set-logic QF_S)
(set-info :status sat)
(set-option :smt.str.ecma_engine_semantics true)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex ecma2020) "\bfoo\b")))
(assert (= x "a foo b"))

(check-sat)
