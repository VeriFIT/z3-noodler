; A backreference inside its own group refers to a group that has not closed yet (issue #476).
; Its capture is undefined there, so \1 matches the empty string.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "a"))
(assert (str.in_re x (re.from_ecma2020 "^(a\1)$")))

(check-sat)
