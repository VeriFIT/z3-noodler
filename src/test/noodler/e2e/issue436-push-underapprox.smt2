; issue 436: an unsat obtained from an underapproximation (str.to_int over an infinite digit
; language, at most 5 digits by default) must not be reported as unsat in incremental mode
(set-info :status unknown)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun n () Int)
(push 1)
(assert (= n (str.to_int (str.++ x y))))
(assert (str.in_re x (re.+ (re.range "0" "9"))))
(assert (> n 123456789))
(check-sat)
(pop 1)
