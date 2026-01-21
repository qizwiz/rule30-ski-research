;;;; brute.lisp - Try brute force for small CA to understand the space

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")

(format t "~%=== BRUTE FORCE SEARCH ===~%~%")

(defun contains-target-p (ca-bits target-bits)
  "Check if target appears EXACTLY in ca-bits at any position."
  (let ((tgt-len (length target-bits))
        (out-len (length ca-bits)))
    (when (>= out-len tgt-len)
      (loop for start from 0 to (- out-len tgt-len)
            when (loop for i below tgt-len
                      always (eql (nth (+ start i) ca-bits)
                                  (nth i target-bits)))
            return start))))

(defun try-all-initial-states (width generations target)
  "Try all possible initial states for small width."
  (let* ((target-bits (ca-search:target-to-bits target))
         (max-state (expt 2 width))
         (found nil))
    (format t "Trying all ~D possible initial states for width ~D...~%"
            max-state width)
    (dotimes (state-num max-state)
      (when (zerop (mod state-num 10000))
        (format t "Progress: ~D/~D~%" state-num max-state))
      (let* ((initial (loop for i from (1- width) downto 0
                           collect (if (logbitp i state-num) 1 0)))
             (ca (rule110:make-ca-from-state (rule110:state-from-bits initial)))
             (final-ca (rule110:run-ca ca generations))
             (output-bits (rule110:ca-to-bits final-ca))
             (pos (contains-target-p output-bits target-bits)))
        (when pos
          (push (list :initial initial
                      :output output-bits
                      :position pos
                      :state-num state-num)
                found))))
    found))

;; Try small widths first
(format t "~%Searching for '()' in Rule 110 outputs...~%~%")

;; Width 16, various generations
(dolist (gens '(5 10 15 20 25 30))
  (format t "~%--- Width 16, ~D generations ---~%" gens)
  (let ((results (try-all-initial-states 16 gens "()")))
    (if results
        (progn
          (format t "FOUND ~D solutions!~%" (length results))
          (format t "First solution:~%")
          (let ((r (first results)))
            (format t "  Initial: ~A~%" (getf r :initial))
            (format t "  Output:  ~A~%" (getf r :output))
            (format t "  Position: ~D~%" (getf r :position)))
          (return))  ; Stop after first success
        (format t "No exact matches found.~%"))))

(quit)
