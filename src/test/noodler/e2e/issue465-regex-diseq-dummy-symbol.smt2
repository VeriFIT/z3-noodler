(set-info :status sat)
(assert (not (= (re.* re.allchar) (re.* (str.to_re "a")))))
(check-sat)
