(set-info :status unsat)
(declare-const x String)
(assert (distinct
  (str.in_re x (re.++ (str.to_re "a") re.all (str.to_re "a")))
  (and (str.prefixof "a" x) (str.suffixof "a" x) (not (= x "a")))))
(check-sat)
