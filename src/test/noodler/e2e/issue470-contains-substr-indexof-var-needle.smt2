; https://github.com/VeriFIT/z3-noodler/issues/470
; The needle is a variable, so n = 1 cannot be compared against |t| syntactically.
; x = y = "ab" is a model: indexof = 0 and substr(x,0,1) = "a" does not contain "ab".
(set-info :status sat)
(declare-const x String)
(declare-const y String)
(assert (= (str.len y) 2))
(assert (str.contains x y))
(assert (not (str.contains (str.substr x 0 (+ 1 (str.indexof x y 0))) y)))
(check-sat)
(get-model)
