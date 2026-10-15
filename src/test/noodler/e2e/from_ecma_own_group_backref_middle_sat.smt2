; A backreference inside its own group matches the empty string (issue #476), also in the middle of the group.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x (re.from_ecma2020 "^(a\1b)$")))

(check-sat)
