; a bounded loop accepts exactly the words of its expansion, also with a body of several final states and a
; nested bounded loop
(set-logic QF_S)
(set-info :status unsat)
(declare-const x String)
(declare-const y String)
(assert (or
  (not (= (str.in_re x ((_ re.loop 1 3) (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))))
          (str.in_re x (re.union
            (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))
            (re.++ (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))
                   (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c")))))
            (re.++ (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))
                   (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c"))))
                   (re.union (str.to_re "a") (re.++ (str.to_re "b") (re.* (str.to_re "c")))))))))
  (not (= (str.in_re y ((_ re.loop 0 2) ((_ re.loop 1 2) (str.to_re "ab"))))
          (str.in_re y (re.union (str.to_re "") (str.to_re "ab") (str.to_re "abab") (str.to_re "ababab") (str.to_re "abababab")))))))
(check-sat)
