; An unreferenced named group is non-capturing, so the negated membership stays regular (issue #474).
; For example, x = "aa" does not match.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (not (str.in_re x (re.from_ecma2020 "^(?<n>a+)b$"))))
(assert (str.prefixof "aa" x))

(check-sat)
