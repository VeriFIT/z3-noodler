; CPython 3.11.2, urllib.parse.urlsplit (CVE-2023-24329).  An app blocks
; dangerous link schemes:
;
;   def is_safe_link(url):
;       return urlsplit(url).scheme not in {"javascript", "data", "vbscript"}
;
; urlsplit:
;   for b in _UNSAFE_URL_BYTES_TO_REMOVE:          # "\t", "\r", "\n"
;       url = url.replace(b, "")
;   i = url.find(':')
;   if i > 0 and url[0].isascii() and url[0].isalpha():
;       for c in url[:i]:
;           if c not in scheme_chars: break
;       else:
;           scheme, url = url[:i].lower(), url[i+1:]
(set-logic QF_SLIA)
(declare-const url String)
(define-fun remove_tabs ((s String)) String           ; drop \t, \r, \n
  (str.replace_all (str.replace_all (str.replace_all s "\u{9}" "") "\u{d}" "") "\u{a}" ""))
(define-fun scheme_of ((u String)) String               ; the scheme part of urlsplit
  (let ((s (str.substr u 0 (str.indexof u ":" 0))))
    (ite (and (str.contains u ":")
              (str.in_re s (re.++ (re.union (re.range "a" "z") (re.range "A" "Z"))
                                  (re.* (re.union (re.range "a" "z") (re.range "A" "Z") (re.range "0" "9")
                                                  (str.to_re "+") (str.to_re "-") (str.to_re "."))))))
         (str.to_lower s)
         "")))
(define-fun c0_or_space () RegLan (re.range "\u{0}" " "))
; lstrip(C0 control or space): url = lead ++ rest, rest does not start with one
(declare-const lead String)
(declare-const rest String)
(assert (= url (str.++ lead rest)))
(assert (str.in_re lead (re.* c0_or_space)))
(assert (not (str.in_re rest (re.++ c0_or_space re.all))))
; The browser (WHATWG URL standard) strips leading C0 controls and spaces,
; removes tabs and newlines, and reads the scheme case-insensitively.
; Does it run a javascript: URL that the blocklist let through?
(assert (str.prefixof "javascript:" (str.to_lower (remove_tabs rest))))
(assert (str.suffixof "alert(1)" url))
(define-fun scheme () String (scheme_of (remove_tabs url)))
(assert (not (= scheme "javascript")))
(assert (not (= scheme "data")))
(assert (not (= scheme "vbscript")))
(check-sat)
(get-model)
