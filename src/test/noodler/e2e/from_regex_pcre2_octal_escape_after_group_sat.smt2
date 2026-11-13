; In PCRE2, \11 is the octal escape of the tab if fewer than 11 capture groups are opened before it.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "a\u{9}"))
(assert (str.in_re x ((_ re.from_regex pcre2) '(a)\11')))

(check-sat)
