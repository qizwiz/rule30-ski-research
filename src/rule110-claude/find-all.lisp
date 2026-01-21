;;;; find-all.lisp - Find all fundamental emergent patterns

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")
(load "/Users/jonathanhill/src/rule110-claude/tiny-ai.lisp")

(format t "~%╔══════════════════════════════════════════════════════════════╗~%")
(format t "║     RULE 110 GENESIS - EMERGENT ENCODING BOOTSTRAP            ║~%")
(format t "╚══════════════════════════════════════════════════════════════╝~%")

;; Define emergent symbols
(defparameter *lparen-bits* '(1 1 0 0 1 1 0 0 0 1 0 0 1 1 0 1))
(defparameter *rparen-bits* '(0 0 0 1 1 1 1 1 0 0 0 1 0 0 1 1))
(defparameter *nil-bits* (append *lparen-bits* *rparen-bits*))

;; Results storage
(defvar *lparen-result* nil)
(defvar *rparen-result* nil)
(defvar *nil-result* nil)

(defun find-pattern (target-bits ca-width ca-generations population max-gens)
  "Find CA initial conditions that produce target as substring."
  (let ((best-score 0)
        (best-initial nil)
        (target-len (length target-bits))
        (pop (loop repeat population collect (loop repeat ca-width collect (random 2)))))

    (dotimes (gen max-gens)
      (let ((scores (mapcar
                     (lambda (initial)
                       (let* ((ca (rule110:make-ca-from-state
                                  (rule110:state-from-bits initial)))
                              (final (rule110:run-ca ca ca-generations))
                              (output (coerce (rule110:ca-state final) 'list)))
                         (loop for start from 0 to (max 0 (- (length output) target-len))
                               maximize (loop for i below target-len
                                             count (eql (nth (+ start i) output)
                                                        (nth i target-bits))))))
                     pop)))

        (loop for init in pop for score in scores
              when (> score best-score)
              do (setf best-score score best-initial (copy-list init)))

        (when (zerop (mod gen 200))
          (format t "  Gen ~4D: ~D/~D~%" gen best-score target-len))

        (when (= best-score target-len)
          (return-from find-pattern (values best-initial best-score t)))

        ;; Next generation
        (let ((new-pop (list best-initial)))
          (loop while (< (length new-pop) population)
                for i1 = (random (length pop))
                for i2 = (random (length pop))
                for parent = (if (> (nth i1 scores) (nth i2 scores))
                                (nth i1 pop) (nth i2 pop))
                for child = (mapcar (lambda (b) (if (< (random 1.0) 0.1) (- 1 b) b)) parent)
                do (push child new-pop))
          (setf pop new-pop))))

    (values best-initial best-score nil)))

(defun verify-pattern (initial target-bits ca-generations)
  "Verify that initial produces target."
  (let* ((ca (rule110:make-ca-from-state (rule110:state-from-bits initial)))
         (final (rule110:run-ca ca ca-generations))
         (output (coerce (rule110:ca-state final) 'list))
         (target-len (length target-bits)))
    (loop for start from 0 to (max 0 (- (length output) target-len))
          when (loop for i below target-len
                    always (eql (nth (+ start i) output) (nth i target-bits)))
          return (values t start output))))

;; === FIND LPAREN ===
(format t "~%~%=== FINDING LPAREN '(' ===~%")
(format t "Target: ~{~A~}~%~%" *lparen-bits*)
(multiple-value-bind (init score success)
    (find-pattern *lparen-bits* 32 40 200 2000)
  (when success
    (setf *lparen-result* init)
    (multiple-value-bind (ok pos output) (verify-pattern init *lparen-bits* 40)
      (format t "~%VERIFIED: Pattern found at position ~D~%" pos)
      (format t "Initial: ~{~A~}~%" init))))

;; === FIND RPAREN ===
(format t "~%~%=== FINDING RPAREN ')' ===~%")
(format t "Target: ~{~A~}~%~%" *rparen-bits*)
(multiple-value-bind (init score success)
    (find-pattern *rparen-bits* 32 40 200 2000)
  (when success
    (setf *rparen-result* init)
    (multiple-value-bind (ok pos output) (verify-pattern init *rparen-bits* 40)
      (format t "~%VERIFIED: Pattern found at position ~D~%" pos)
      (format t "Initial: ~{~A~}~%" init))))

;; === FIND NIL (both patterns in sequence) ===
(format t "~%~%=== FINDING NIL '()' ===~%")
(format t "Target: ~{~A~}~%" *nil-bits*)
(format t "(This is 32 bits - lparen concatenated with rparen)~%~%")
(multiple-value-bind (init score success)
    (find-pattern *nil-bits* 64 50 300 5000)
  (if success
      (progn
        (setf *nil-result* init)
        (multiple-value-bind (ok pos output) (verify-pattern init *nil-bits* 50)
          (format t "~%*** VERIFIED: NIL PATTERN FOUND! ***~%")
          (format t "Position: ~D~%" pos)
          (format t "Initial: ~{~A~}~%" init)))
      (format t "~%Best score: ~D/32 - need more search~%" score)))

;; === SUMMARY ===
(format t "~%~%╔══════════════════════════════════════════════════════════════╗~%")
(format t "║                     DISCOVERY SUMMARY                          ║~%")
(format t "╚══════════════════════════════════════════════════════════════╝~%")
(format t "~%Emergent encoding (Rule 110's natural patterns):~%")
(format t "  '(' = ~{~A~}~%" *lparen-bits*)
(format t "  ')' = ~{~A~}~%" *rparen-bits*)
(format t "~%Discovered Tiny AIs:~%")
(when *lparen-result*
  (format t "  LPAREN: ~{~A~}~%" *lparen-result*))
(when *rparen-result*
  (format t "  RPAREN: ~{~A~}~%" *rparen-result*))
(when *nil-result*
  (format t "  NIL:    ~{~A~}~%" *nil-result*))

(quit)
