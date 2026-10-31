; A membership in a re.comp of a re.union of re.from_ecma2020 regexes is split into the negated disjunction of
; the memberships (issue #522). Of the strings in [a-c], only x = "c" matches neither pattern.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x (re.comp (re.union (re.from_ecma2020 "a") (re.from_ecma2020 "b")))))
(assert (str.in_re x (re.range "a" "c")))

(check-sat)
