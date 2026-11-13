; In PCRE2, \h matches also non-ASCII horizontal white space, e.g., the no-break space, which \s does not match.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "a\u{a0}b"))
(assert (str.in_re x ((_ re.from_regex pcre2) 'a\hb')))
(assert (not (str.in_re x ((_ re.from_regex pcre2) 'a\sb'))))

(check-sat)
