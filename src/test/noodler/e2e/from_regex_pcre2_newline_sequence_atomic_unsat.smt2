; In PCRE2, \R is atomic: it matches the whole \r\n, so nothing is left for the following \n.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "\u{d}\u{a}"))
(assert (str.in_re x ((_ re.from_regex pcre2) '\R\n')))

(check-sat)
