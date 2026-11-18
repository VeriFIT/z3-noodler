; Jinja2 3.1.3, the fix of CVE-2024-22195: keys with white space are rejected.
;
;   _space_re = re.compile(r"\s", flags=re.ASCII)
;   if _space_re.search(key) is not None:
;       raise ValueError(f"Spaces are not allowed in attributes: '{key}'")
(set-logic QF_SLIA)
(declare-const key String)
(define-fun escape ((s String)) String   ; markupsafe.escape
  (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all s
    "&" "&amp;") ">" "&gt;") "<" "&lt;") "\u{27}" "&#39;") "\u{22}" "&#34;"))
(assert (not (str.in_re key (re.++ re.all (re.union (str.to_re " ") (re.range "\u{9}" "\u{d}")) re.all))))
; In HTML, an attribute name ends at a tab, LF, FF, space, "/", "=" or ">".
; Can the key smuggle in a second attribute, an event handler?
(assert (str.in_re (escape key)
  (re.++ re.all (re.union (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}")
                          (str.to_re " ") (str.to_re "/"))
         (str.to_re "onmouseover"))))
(check-sat)
(get-model)
