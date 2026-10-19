; x = y merges the literals "foo" and "bar", which have the same length, and by congruence the re.from_ecma2020
; terms (issue #521).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)
(declare-const y String)

(assert (str.in_re x (re.from_ecma2020 "foo")))
(assert (str.in_re y (re.from_ecma2020 "bar")))
(assert (= x y))

(check-sat)
