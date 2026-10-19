; The membership in re.inter is split into memberships of x in both literal patterns (issue #522), whose literals
; are then merged together with the re.from_ecma2020 terms (issue #521).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x (re.inter (re.from_ecma2020 "a") (re.from_ecma2020 "b"))))

(check-sat)
