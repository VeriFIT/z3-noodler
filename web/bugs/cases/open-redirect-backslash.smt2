; A "fix" after the first bug report: also check with backslashes turned
; into slashes.
;
;   def is_safe_redirect(url):
;       u = url.replace("\\", "/")
;       return u.startswith("/") and not u.startswith("//")
;
; Is that enough?
(set-logic QF_SLIA)
(declare-const url String)
(define-fun browser ((s String)) String
  (str.replace_all
    (str.replace_all (str.replace_all (str.replace_all s "\u{9}" "") "\u{a}" "") "\u{d}" "")
    "\u{5c}" "/"))
(define-fun u () String (str.replace_all url "\u{5c}" "/"))
(assert (str.prefixof "/" u))
(assert (not (str.prefixof "//" u)))
(assert (str.prefixof "//" (browser url)))
(check-sat)
(get-model)
