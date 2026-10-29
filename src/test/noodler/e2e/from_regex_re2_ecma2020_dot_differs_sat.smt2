; The dot of RE2 matches \r, the dot of ECMAScript 2020 does not.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex re2) ".")))
(assert (not (str.in_re x ((_ re.from_regex ecma2020) "."))))

(check-sat)
(get-model)
