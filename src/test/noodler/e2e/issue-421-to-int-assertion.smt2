; https://github.com/VeriFIT/z3-noodler/issues/421
; Used to trigger an assertion failure ("minus_one_possible") in
; ConversionHandler::get_to_int_value_bounds (conversion_handler.cpp). The speculative
; length pre-check in DecisionProcedure::get_initial_lengths calls this function with the
; raw (not-yet-preprocessed) automaton assignment, where a to_int conversion's string
; variable can legitimately have an empty-language automaton (e.g. because the SAT core is
; currently exploring a branch where `v` is speculatively required to contain "n", which is
; incompatible with the digit-only membership constraint). This does not mean the formula is
; unsatisfiable overall, so the code must not assert that it can't happen.
(set-logic QF_SLIA)
(set-info :status sat)
(declare-const v String)
(declare-const on Int)
(assert (= "" (ite false (str.at v 1) (let ((p0 (str.indexof (let ((p0 (str.indexof v "n" 0))) (str.substr v 0 p0)) ":" 0))) (str.substr (str.at v 1) 0 p0)))))
(assert (str.in_re v (re.range "0" "9")))
(assert (= on (str.to_int v)))
(assert (> on 0))
(check-sat)
