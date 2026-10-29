; QF_SLIA/20190311-str-small-rw-Noetzli/str-term-small-rw/str-term-small-rw_366.smt2. Premature length checks prune
; here, and the loop protection kept blocking unsat cores of the rewritten blocked length formula, which the SAT solver
; satisfied by falsifying that formula with its auxiliary variables, so it never finished.
(set-info :status unsat)
(set-option :timeout 60000)
(declare-fun x () String)
(declare-fun z () Int)
(assert (not (= (str.substr (str.++ "B" x) z z) (str.substr x (- z 1) z))))
(check-sat)
