; In PCRE2, \R matches a newline sequence, the only one with two characters is \r\n.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex pcre2) 'a\Rb')))
(assert (= (str.len x) 4))
(assert (= (str.at x 1) "\u{d}"))

(check-sat)
