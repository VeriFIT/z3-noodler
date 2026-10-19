; The branch x = y merges the literals "a" and "b" and, by congruence, the re.from_ecma2020 terms. The branch has to
; be refuted so that the search continues with p (issue #521). For example, x = "a", y = "b" and p is true.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)
(declare-const y String)
(declare-const p Bool)

(assert (str.in_re x (re.from_ecma2020 "a")))
(assert (str.in_re y (re.from_ecma2020 "b")))
(assert (or (= x y) p))

(check-sat)
