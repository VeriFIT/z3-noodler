; A re.diff of a re.from_ecma2020 regex and a re.union mixing re.from_ecma2020 with an ordinary regex is
; rewritten to a re.inter with a re.comp, and the membership in it is split into memberships (issue #522).
; Of the strings in [a-c], only x = "c" is neither "a" nor "b".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.diff (re.from_ecma2020 "[a-c]") (re.union (re.from_ecma2020 "a") (str.to_re "b")))))

(check-sat)
