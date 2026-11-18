; The fix: an allow-list of characters instead of a deny-list of prefixes.
;
;   SAFE = re.compile(r"/(?:[A-Za-z0-9._~-][A-Za-z0-9._~/-]*)?(?:\?[A-Za-z0-9=&._~-]*)?")
;   def is_safe_redirect(url):
;       return SAFE.fullmatch(url) is not None
;
; Can an accepted url go to another host?  (unsat = no)
(set-logic QF_SLIA)
(declare-const url String)
(define-fun browser ((s String)) String
  (str.replace_all
    (str.replace_all (str.replace_all (str.replace_all s "\u{9}" "") "\u{a}" "") "\u{d}" "")
    "\u{5c}" "/"))
(assert (str.in_re url (re.from_ecma2020 '/(?:[A-Za-z0-9._~-][A-Za-z0-9._~/-]*)?(?:\?[A-Za-z0-9=&._~-]*)?')))
(assert (str.prefixof "//" (browser url)))
(check-sat)
