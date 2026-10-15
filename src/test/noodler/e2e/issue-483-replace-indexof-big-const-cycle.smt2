(set-info :status sat)
; model generation used to fail on the concatenation ("" ++ substr ++ post_substr) whose class contains substr
(declare-fun x () String)
(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (= (str.replace (str.substr x 0 (+ 4294967297 (str.indexof x "b" 0))) "b" "c") x))
(check-sat)
