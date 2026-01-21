;;;; discover.lisp - Discover what patterns Rule 110 naturally produces
;;;; Maybe we shouldn't force ASCII - let the encoding emerge!

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")

(format t "~%=== DISCOVERING RULE 110'S NATURAL VOCABULARY ===~%~%")

(defun hash-bits (bits)
  "Create a hash key from a bit list."
  (format nil "~{~A~}" bits))

(defun discover-patterns (width generations num-samples)
  "Sample random initial states and collect unique outputs."
  (let ((patterns (make-hash-table :test 'equal)))
    (dotimes (i num-samples)
      (let* ((initial (loop repeat width collect (random 2)))
             (ca (rule110:make-ca-from-state (rule110:state-from-bits initial)))
             (final-ca (rule110:run-ca ca generations))
             (output-bits (rule110:ca-to-bits final-ca))
             (key (hash-bits output-bits)))
        (if (gethash key patterns)
            (incf (gethash key patterns))
            (setf (gethash key patterns) 1))))
    patterns))

;; Discover patterns for width 16
(format t "~%=== WIDTH 16, 20 GENERATIONS ===~%")
(let* ((patterns (discover-patterns 16 20 10000))
       (sorted (sort (loop for k being the hash-keys of patterns
                          using (hash-value v)
                          collect (cons k v))
                    #'> :key #'cdr)))
  (format t "~%Unique patterns found: ~D~%" (hash-table-count patterns))
  (format t "~%Top 10 most common patterns:~%")
  (loop for (pattern . count) in (subseq sorted 0 (min 10 (length sorted)))
        for i from 1
        do (format t "~2D. (~4D times) ~A~%" i count pattern)))

;; Now try to find a PAIR of patterns we can use as ( and )
(format t "~%~%=== LOOKING FOR SYMBOL PAIRS ===~%")
(format t "We need two distinct patterns to represent '(' and ')'~%")
(format t "Let's find the TWO most common stable patterns...~%~%")

(let* ((patterns-20 (discover-patterns 16 20 10000))
       (patterns-40 (discover-patterns 16 40 10000))
       (sorted-20 (sort (loop for k being the hash-keys of patterns-20
                             using (hash-value v)
                             collect (cons k v))
                       #'> :key #'cdr))
       (sorted-40 (sort (loop for k being the hash-keys of patterns-40
                             using (hash-value v)
                             collect (cons k v))
                       #'> :key #'cdr)))
  (format t "After 20 generations:~%")
  (loop for (p . c) in (subseq sorted-20 0 5)
        do (format t "  ~A (count: ~D)~%" p c))
  (format t "~%After 40 generations:~%")
  (loop for (p . c) in (subseq sorted-40 0 5)
        do (format t "  ~A (count: ~D)~%" p c))

  ;; Pick first two as our symbols!
  (let ((lparen (caar sorted-40))
        (rparen (caadr sorted-40)))
    (format t "~%~%=== PROPOSED EMERGENT ENCODING ===~%")
    (format t "'(' := ~A~%" lparen)
    (format t "')' := ~A~%" rparen)
    (format t "~%These are the patterns Rule 110 naturally produces!~%")
    (format t "Now we can define NIL as the CA that produces: ~A~A~%"
            lparen rparen)))

(quit)
