;;;; test.lisp - Quick test script

;;; Load all files
(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")
(load "/Users/jonathanhill/src/rule110-claude/tiny-ai.lisp")
(load "/Users/jonathanhill/src/rule110-claude/genesis.lisp")

;;; Show the vision
(genesis:explain)

;;; Demo Rule 110
(genesis:demo-rule110)

;;; Try to find NIL
(format t "~%~%=== ATTEMPTING TO BOOTSTRAP NIL ===~%")
(tiny-ai:bootstrap-nil)

;;; Show what we found
(genesis:status)

;;; If we found it, verify it works
(let ((nil-ai (tiny-ai:find-tiny-ai "nil")))
  (when nil-ai
    (format t "~%~%=== VERIFICATION ===~%")
    (format t "Running tiny AI 'nil'...~%")
    (format t "Output: ~S~%" (tiny-ai:run-tiny-ai nil-ai))
    (format t "~%FIRST TINY AI VERIFIED!~%")))

(quit)
