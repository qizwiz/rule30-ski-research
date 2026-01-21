;;;; verify.lisp - Verify our emergent pattern discovery

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")

(defparameter *lparen-bits* '(1 1 0 0 1 1 0 0 0 1 0 0 1 1 0 1))

;; The initial state that was found
(defparameter *found-initial* '(1 1 1 0 1 1 1 0 0 0 0 1 1 0 0 0 1 0 0 1 0 1 1 0 0 1 0 1 0 1 1 0))

(format t "~%=== VERIFICATION ===~%~%")
(format t "Target pattern (lparen): ~{~A~}~%" *lparen-bits*)
(format t "Found initial state:     ~{~A~}~%" *found-initial*)

;; Run the CA
(let* ((ca (rule110:make-ca-from-state (rule110:state-from-bits *found-initial*)))
       (final (rule110:run-ca ca 40))
       (output (rule110:ca-to-bits final))
       (target *lparen-bits*))
  (format t "~%Output after 40 gens:    ~{~A~}~%" output)
  (format t "~%Checking all 16-bit windows for exact match:~%")

  ;; Check each window
  (loop for start from 0 to (- (length output) 16)
        for window = (subseq output start (+ start 16))
        for matches = (loop for i below 16
                           count (eql (nth i window) (nth i target)))
        do (format t "  Position ~2D: ~{~A~} - ~D/16 match~A~%"
                  start window matches
                  (if (= matches 16) " *** EXACT MATCH! ***" ""))))

(quit)
