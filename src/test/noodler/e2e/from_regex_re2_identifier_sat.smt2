; RE2 ASCII and Perl classes, e.g., x = "_a9".
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex re2) '[[:alpha:]_]\w*')))
(assert (= (str.len x) 3))
(assert (str.contains x "9"))

(check-sat)
