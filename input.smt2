(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)

(assert (= (str.++ x y) (str.++ y x)))
(assert (= z (str.++ x y)))

(assert (str.in_re x (re.from_ecma2020 "[^\]\--/a-z^\b--\0-\37\cZ]")))

(assert (> (str.len z) 5))
(assert (not (str.contains y "b")))

(check-sat)