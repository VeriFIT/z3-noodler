; In PCRE2, the dot does not match \n without the flag s.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex pcre2) "a.b")))
(assert (str.contains x "\u{a}"))

(check-sat)
