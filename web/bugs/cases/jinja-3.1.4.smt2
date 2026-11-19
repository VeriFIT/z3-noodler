; Jinja2 3.1.4, the fix of CVE-2024-34064: also reject "/", ">" and "=".
;
;   _attr_key_re = re.compile(r"[\s/>=]", flags=re.ASCII)
;   if _attr_key_re.search(key) is not None:
;       raise ValueError(f"Invalid character in attribute name: {key!r}")
;
; (unsat = no key gets past the check and injects an attribute)
(set-logic QF_SLIA)
(declare-const key String)
(define-fun escape ((s String)) String   ; markupsafe.escape
  (str.replace_all (str.replace_all (str.replace_all (str.replace_all (str.replace_all s
    "&" "&amp;") ">" "&gt;") "<" "&lt;") "\u{27}" "&#39;") "\u{22}" "&#34;"))
(assert (not (str.in_re key (re.++ re.all (re.union (str.to_re " ") (re.range "\u{9}" "\u{d}")
                                                    (str.to_re "/") (str.to_re ">") (str.to_re "=")) re.all))))
; In HTML, an attribute name ends at a tab, LF, FF, space, "/", "=" or ">".
; Can the key smuggle in a second attribute, an event handler?
(assert (str.in_re (escape key)
  (re.++ re.all (re.union (str.to_re "\u{9}") (str.to_re "\u{a}") (str.to_re "\u{c}")
                          (str.to_re " ") (str.to_re "/"))
         (str.to_re "onmouseover"))))
(check-sat)
