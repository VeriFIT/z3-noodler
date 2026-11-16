; issue 436: the second call reuses the lemmas of the first one (loop protection), both must stay inconclusive
(set-info :status unknown)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.in_re x (re.+ (re.range "0" "9"))))
(check-sat-assuming ((> (str.to_int (str.++ x y)) 123456789)))
(check-sat-assuming ((> (str.to_int (str.++ x y)) 123456789)))
