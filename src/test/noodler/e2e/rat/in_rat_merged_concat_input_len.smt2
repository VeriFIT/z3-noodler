(set-option :produce-models true)
(set-info :status sat)
(declare-const x String)
(declare-const y String)

; Same shape as in_rat_merged_concat_input.smt2, but with an extra length
; constraint on x. This used to make get_model intersect an empty language
; (T^-1(model(y)) with L(x)) and crash with an uncaught
; std::bad_optional_access instead of answering sat.
(assert (str.in_rat (str.++ "b" x) y (rat.* (rat.union (str.to_rat "a" "b") (str.to_rat "b" "a")))))
(assert (= (str.len x) 1))

(check-sat)
(get-model)
