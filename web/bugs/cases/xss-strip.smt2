; XSS: a "sanitizer" that deletes <script> tags from a comment before it is
; put into an HTML page.
;
;   function sanitize(comment) {
;     return comment.replaceAll("<script>", "");
;   }
;
; HTML tag names are case-insensitive, so the browser runs a script if the
; lower-cased output contains "<script>".  Can that happen?
(set-logic QF_SLIA)
(declare-const comment String)
(define-fun out () String (str.replace_all comment "<script>" ""))
(assert (str.contains (str.to_lower out) "<script>"))
(check-sat)
(get-model)
