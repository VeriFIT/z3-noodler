; Negation of a regular from_ecma2020 pattern becomes the disequation x != "a",
; which together with x in a|aaaa and |x| < 3 is unsatisfiable.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (not (str.in_re x (re.from_ecma2020 "a"))))
(assert (str.in_re x (re.union (str.to_re "a") (str.to_re "aaaa"))))
(assert (< (str.len x) 3))

(check-sat)
