; In RE2, the text between \Q and \E is literal.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex re2) '\Qa.b\E')))
(assert (not (= x "a.b")))

(check-sat)
