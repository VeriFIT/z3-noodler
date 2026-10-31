; A membership in re.from_ecma2020 must not be merged with a membership of the same string in an ordinary
; regex into a re.union (issue #522). Only the second disjunct allows length 2, so x = "bb".
(set-logic QF_SLIA)
(set-info :status sat)

(declare-const x String)

(assert (or (str.in_re x (re.from_ecma2020 "a")) (str.in_re x (re.* (str.to_re "b")))))
(assert (= (str.len x) 2))

(check-sat)
