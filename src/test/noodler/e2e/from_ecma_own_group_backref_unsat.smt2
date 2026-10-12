; A backreference inside its own group matches the empty string (issue #476), not the part of the group before it.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "aa"))
(assert (str.in_re x (re.from_ecma2020 "^(a\1)$")))

(check-sat)
