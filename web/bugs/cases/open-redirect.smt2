; Open redirect: after login, the app redirects to ?next=<url>.  To stay on
; the same site, it accepts paths but not protocol-relative URLs (//host).
;
;   def is_safe_redirect(url):
;       return url.startswith("/") and not url.startswith("//")
;
; What the browser makes of the URL (WHATWG URL standard): it removes tabs
; and newlines, and treats "\" like "/".  Can it start with "//", i.e. go to
; another host?
(set-logic QF_SLIA)
(declare-const url String)
(define-fun browser ((s String)) String
  (str.replace_all
    (str.replace_all (str.replace_all (str.replace_all s "\u{9}" "") "\u{a}" "") "\u{d}" "")
    "\u{5c}" "/"))
(assert (str.prefixof "/" url))
(assert (not (str.prefixof "//" url)))
(assert (str.prefixof "//" (browser url)))
(check-sat)
(get-model)
