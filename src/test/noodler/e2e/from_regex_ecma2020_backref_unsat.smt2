; x = "ab" does not match ^(a)\1$ given by re.from_regex with the ecma2020 flavor.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (= x "ab"))
(assert (str.in_re x ((_ re.from_regex ecma2020) "^(a)\1$")))

(check-sat)
