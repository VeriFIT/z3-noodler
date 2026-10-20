; RE2 counted repetition: (ab){2,3} matches strings of length 4 or 6.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex re2) "(ab){2,3}")))
(assert (= (str.len x) 5))

(check-sat)
