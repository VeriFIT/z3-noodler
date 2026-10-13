; '.*' cannot match a string with a line terminator (issue #454).
(set-logic QF_S)
(set-info :status unsat)

(declare-const x String)

(assert (str.in_re x (re.from_ecma2020 "^a.*b$")))
(assert (str.contains x "\u{a}"))

(check-sat)
