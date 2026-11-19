; A common "fix": run the filter twice.
;
;   name = name.replace("../", "").replace("../", "")
;
; Is the double filter safe?
(set-logic QF_SLIA)
(declare-const name String)
(define-fun once ((s String)) String (str.replace_all s "../" ""))
(assert (str.contains (once (once name)) "../"))
(check-sat)
(get-model)
