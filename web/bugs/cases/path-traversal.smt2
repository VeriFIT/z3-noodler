; Path traversal: a filter that deletes "../" from a user-supplied file name.
;
;   def safe_open(name):
;       name = name.replace("../", "")
;       return open(os.path.join(UPLOAD_DIR, name))
;
; Can the cleaned name still climb out of UPLOAD_DIR?
(set-logic QF_SLIA)
(declare-const name String)                                 ; attacker-controlled
(define-fun cleaned () String (str.replace_all name "../" ""))
(assert (str.contains cleaned "../"))
(check-sat)
(get-model)
