; In RE2, '.' does not match \n without the flag s.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "a\u{a}b"))
(assert (str.in_re x ((_ re.from_regex re2) "a.b")))

(check-sat)
