; ((_ re.from_regex ecma2020) pattern) gives an ECMAScript 2020 regex, here with a backreference.
(set-logic QF_S)
(set-info :status sat)

(declare-const x String)

(assert (str.in_re x ((_ re.from_regex ecma2020) '(a*b)\1')))
(assert (>= (str.len x) 4))

(check-sat)
(get-model)
