; The developer adds case folding: lower-case first, then delete the tags.
;
;   function sanitize(comment) {
;     return comment.toLowerCase().replaceAll("<script>", "");
;   }
;
; Still exploitable?
(set-logic QF_SLIA)
(declare-const comment String)
(define-fun out () String (str.replace_all (str.to_lower comment) "<script>" ""))
(assert (str.contains out "<script>"))
(check-sat)
(get-model)
