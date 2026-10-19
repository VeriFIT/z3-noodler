(set-info :status unsat)
(assert (= re.allchar (str.to_re "a")))
(check-sat)
