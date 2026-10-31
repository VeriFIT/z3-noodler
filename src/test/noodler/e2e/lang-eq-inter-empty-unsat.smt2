(set-logic QF_S)
(set-info :status unsat)
; the intersection holds "ab" and longer words
(assert (= (re.inter (re.++ (str.to_re "a") (re.* re.allchar)) (re.++ (re.* re.allchar) re.allchar (str.to_re "b"))) re.none))
(check-sat)
