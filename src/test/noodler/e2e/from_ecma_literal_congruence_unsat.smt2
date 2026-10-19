; The memberships equate x with both literals "a" and "b". Merging the literals also merges the re.from_ecma2020
; terms by congruence, which must not make the final check give up (issue #521).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "a")))
(assert (str.in_re x (re.from_ecma2020 "b")))

(check-sat)
