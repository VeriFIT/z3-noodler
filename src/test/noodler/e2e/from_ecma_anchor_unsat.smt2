; The anchor ^ requires the prefix before it to be empty, which the preceding b prevents.
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "b^a")))

(check-sat)
