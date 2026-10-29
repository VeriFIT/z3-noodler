(set-info :status unsat)
; str-pred-small-rw_702 (Noetzli): the solving states of x = l y r = l' y r' used to be generated forever, although
; the substitutions of each of them make the needle y of not(contains(l' x r', y)) occur in its haystack
(set-option :timeout 20000)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (str.contains (str.replace x y x) y) (str.contains x y))))
(check-sat)
