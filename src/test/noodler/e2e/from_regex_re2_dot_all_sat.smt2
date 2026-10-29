; In RE2, '.' matches \n with the flag s.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "a\u{a}b"))
(assert (str.in_re x ((_ re.from_regex re2) "(?s)a.b")))

(check-sat)
