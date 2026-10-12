; Every iteration captures "a" and its lookahead sees "a" at the next position (issue #457).
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "aaa"))
(assert (str.in_re x (re.from_ecma2020 "^(?:(\w)(?=\1)){2}\w$")))

(check-sat)
