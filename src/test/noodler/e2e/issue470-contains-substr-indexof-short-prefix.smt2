; https://github.com/VeriFIT/z3-noodler/issues/470
; contains(substr(x,0,n+indexof(x,t,0)),t) <=> indexof(x,t,0) != -1 only holds for n >= |t|.
; Here n = 1 < |t| = 2, so x = "ab" is a model: indexof = 0 and substr(x,0,1) = "a".
(set-info :status sat)
(declare-const x String)
(assert (not (str.contains (str.substr x 0 (+ 1 (str.indexof x "ab" 0))) "ab")))
(assert (str.contains x "ab"))
(check-sat)
(get-model)
