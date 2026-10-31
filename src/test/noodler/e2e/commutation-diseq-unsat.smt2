(set-logic QF_SLIA)
(set-info :status unsat)
; Noetzli str-pred-small-rw_142: both sides hold iff x in A*; needs the disequation of not(suffixof) to prune
(declare-fun x () String)
(assert (not (= (str.prefixof x (str.++ "A" x)) (str.suffixof x (str.++ x "A")))))
(check-sat)
