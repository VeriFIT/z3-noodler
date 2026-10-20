; In RE2, a negated character class matches \n.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (= x "\u{a}"))
(assert (str.in_re x ((_ re.from_regex re2) "[^a]")))

(check-sat)
