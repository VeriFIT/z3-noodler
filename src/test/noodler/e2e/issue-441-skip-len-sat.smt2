; Issue #441: wrong SAT without model generation: skip_len_sat did not mark kept-side vars as length
; when the removed (left) side contained a length variable (the harness runs with model=true, so the
; regression is covered by the "Skip len sat" unit test).
(set-info :status unsat)
(set-logic QF_SLIA)
(declare-fun Y1 () String)(declare-fun Y2 () String)(declare-fun Z () String)
(declare-fun X () String)(declare-fun k () Int)
(assert (str.in_re (str.++ Y1 Y2) (re.* re.allchar)))
(assert (or (= Z "zzz") (and (= (str.++ Y1 Y2) Z) (= Z (str.++ "b" X)))))
(assert (str.in_re Z (re.union (re.* (str.to_re "aa")) (str.to_re "b"))))
(assert (str.in_re X (re.* (str.to_re "a"))))
(assert (= (str.len Y1) (* 2 k)))
(assert (> k 0))
(check-sat)
