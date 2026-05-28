; Regression test for GitHub issue #370
; Incremental formula with str.to_code(ite(...)) causes uncaught exception:
;   libc++abi: terminating due to uncaught exception of type std::out_of_range: unordered_map::at: key not found
;
; Root cause: after push/pop, the preprocessing step substitute_var() can map a
; conversion's string_var to a Literal. conversions_validity() then calls
; aut_ass.at(literal) which crashes because aut_ass only stores Variable keys.
;
; The test uses multiple push/pop/check-sat blocks with a str.to_code(ite(...))
; assertion at the base level and str.substr assertions inside pushed scopes.
; The crash manifests on the third check-sat.
(set-logic ALL)
(set-info :status sat)
(declare-fun |stdin0| () String)
(declare-fun |n| () Int)

(push 1)
(check-sat)
(pop 1)
(assert (not (>= (str.to_code (ite (= 0 n) "a" "b")) 256)))
(push 1)
(assert (= "cd" (str.substr stdin0 2 2)))
(check-sat)
(pop 1)
(push 1)
(assert (= "ab" (str.substr stdin0 0 2)))
(check-sat)
(pop 1)
