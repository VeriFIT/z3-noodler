; re.from_ecma2020 is a synonym of re.from_regex with the ecma2020 flavor, so both memberships are the same atom.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex ecma2020) "(a*b)\1")))
(assert (not (str.in_re x (re.from_ecma2020 "(a*b)\1"))))

(check-sat)
