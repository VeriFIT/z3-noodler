; The fix: escape "<" instead of deleting tags.
;
;   function sanitize(comment) {
;     return comment.replaceAll("<", "&lt;");
;   }
;
; Can the output contain any tag opening at all?  (unsat = no)
(set-logic QF_SLIA)
(declare-const comment String)
(define-fun out () String (str.replace_all comment "<" "&lt;"))
(assert (str.contains out "<"))
(check-sat)
