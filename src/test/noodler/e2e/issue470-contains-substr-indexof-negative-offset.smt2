; https://github.com/VeriFIT/z3-noodler/issues/470
; n = -4294967295 is truncated to 1 by get_int32(), so the special case wrongly fires.
; x = "a" is a model: indexof = 0, the substring length is negative, so substr(x,0,n) = "".
(set-info :status sat)
(declare-const x String)
(assert (not (str.contains (str.substr x 0 (+ (- 4294967295) (str.indexof x "a" 0))) "a")))
(assert (str.contains x "a"))
(check-sat)
(get-model)
