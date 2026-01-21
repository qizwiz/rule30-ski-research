;;;; test2.lisp - More aggressive search for NIL

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")
(load "/Users/jonathanhill/src/rule110-claude/tiny-ai.lisp")

(format t "~%=== AGGRESSIVE SEARCH FOR NIL ===~%")
(format t "Larger CA, more generations, higher mutation~%~%")

;; Increase mutation rate to escape local optima
(setf ca-search:*mutation-rate* 0.1)

;; Try with more aggressive parameters
(let ((result (ca-search:find-ca-for-target "()"
                                            :ca-width 48        ; wider CA
                                            :ca-generations 30  ; more CA steps
                                            :population-size 200
                                            :max-generations 2000)))
  (if (= (ca-search:search-result-fitness result) 16)
      (progn
        (format t "~%*** SUCCESS! ***~%")
        (format t "Initial state: ~A~%" (ca-search:search-result-initial-state result))
        ;; Verify
        (let* ((ca (rule110:make-ca-from-state
                    (rule110:state-from-bits (ca-search:search-result-initial-state result))))
               (final-ca (rule110:run-ca ca 30)))
          (format t "~%Output verification:~%")
          (format t "Final CA state: ~A~%" (rule110:ca-to-bits final-ca))
          (format t "As string: ~S~%" (rule110:ca-to-string final-ca))))
      (format t "~%Best: ~D/16~%" (ca-search:search-result-fitness result))))

(quit)
