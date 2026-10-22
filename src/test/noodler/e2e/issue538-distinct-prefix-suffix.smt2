(set-info :status unsat)
(set-logic QF_S)
(declare-const x String)
; g = ab*bc
(define-fun g () Bool (str.in_re x (re.++ (str.to_re "ab") re.all (str.to_re "bc"))))
; e = ab* & *bc & !abc
(define-fun e () Bool (and (str.prefixof "ab" x) (str.suffixof "bc" x) (not (= x "abc"))))
(assert (distinct g e))
(check-sat)
