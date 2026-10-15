; Only the open group is undefined (issue #476): group 2 is closed, so \2 matches "b", while \1 inside group 1
; matches the empty string.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "abb"))
(assert (str.in_re x (re.from_ecma2020 "^(a(b)\2\1)$")))

(check-sat)
