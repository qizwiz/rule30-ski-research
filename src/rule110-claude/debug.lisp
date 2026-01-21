;;;; debug.lisp - Debug the search to understand the local optimum

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")

(format t "~%=== DEBUGGING THE SEARCH ===~%~%")

;; Run a quick search and examine what we get
(setf ca-search:*mutation-rate* 0.15)

(let* ((result (ca-search:find-ca-for-target "()"
                                             :ca-width 32
                                             :ca-generations 20
                                             :population-size 100
                                             :max-generations 300))
       (initial (ca-search:search-result-initial-state result))
       (ca (rule110:make-ca-from-state (rule110:state-from-bits initial)))
       (final-ca (rule110:run-ca ca 20))
       (output-bits (rule110:ca-to-bits final-ca))
       (target-bits (ca-search:target-to-bits "()")))

  (format t "~%Initial state: ~A~%" initial)
  (format t "~%Output bits:   ~A~%" output-bits)
  (format t "Target bits:   ~A~%" target-bits)

  ;; Show actual string output
  (format t "~%Attempting ASCII interpretation of full output:~%")
  (let ((output-str (rule110:ca-to-string final-ca)))
    (format t "Raw string: ~S~%" output-str)
    (format t "Char codes: ")
    (loop for char across output-str
          do (format t "~D " (char-code char)))
    (format t "~%"))

  ;; Show what each 8-bit window looks like
  (format t "~%All 8-bit windows in output:~%")
  (let ((bits output-bits))
    (loop for i from 0 to (- (length bits) 8)
          for window = (subseq bits i (+ i 8))
          for byte = (loop for j from 0 below 8
                          sum (* (nth j window) (expt 2 (- 7 j))))
          when (and (>= byte 32) (<= byte 126))
          do (format t "  Position ~2D: ~A = '~A' (target '(' = ~A, ')' = ~A)~%"
                    i window (code-char byte)
                    (ca-search:target-to-bits "(")
                    (ca-search:target-to-bits ")")))))

(quit)
