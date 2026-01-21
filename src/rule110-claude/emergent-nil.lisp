;;;; emergent-nil.lisp - Find CA that produces emergent NIL encoding
;;;; The encoding emerges from Rule 110's natural dynamics!

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/search.lisp")
(load "/Users/jonathanhill/src/rule110-claude/tiny-ai.lisp")

(format t "~%╔══════════════════════════════════════════════════════════════╗~%")
(format t "║         EMERGENT ENCODING - RULE 110 GENESIS                  ║~%")
(format t "╚══════════════════════════════════════════════════════════════╝~%")

;; Define our emergent symbols - patterns Rule 110 naturally produces
(defparameter *lparen-bits* '(1 1 0 0 1 1 0 0 0 1 0 0 1 1 0 1))  ; most common after 40 gens
(defparameter *rparen-bits* '(0 0 0 1 1 1 1 1 0 0 0 1 0 0 1 1))  ; second most common

;; NIL = "()" = lparen followed by rparen
(defparameter *nil-bits* (append *lparen-bits* *rparen-bits*))

(format t "~%EMERGENT SYMBOLS (what Rule 110 WANTS to produce):~%")
(format t "  '('  = ~{~A~}~%" *lparen-bits*)
(format t "  ')'  = ~{~A~}~%" *rparen-bits*)
(format t "  NIL  = ~{~A~}~%" *nil-bits*)
(format t "~%NIL is 32 bits = concatenation of two 16-bit symbols~%")

;; Search function for emergent patterns
(defun search-for-emergent-pattern (target-bits
                                    &key (ca-width 48) (ca-generations 40)
                                         (population 300) (max-gens 3000))
  "Search for CA initial conditions that produce target-bits as substring."
  (let ((best-score 0)
        (best-initial nil)
        (target-len (length target-bits))
        (population-list (loop repeat population
                              collect (loop repeat ca-width collect (random 2)))))
    (dotimes (gen max-gens)
      ;; Evaluate fitness
      (let ((scores (mapcar (lambda (initial)
                             (let* ((ca (rule110:make-ca-from-state
                                        (rule110:state-from-bits initial)))
                                    (final (rule110:run-ca ca ca-generations))
                                    (output (rule110:ca-to-bits final)))
                               ;; Count matching bits at best position
                               (loop for start from 0 to (max 0 (- (length output) target-len))
                                     maximize (loop for i below target-len
                                                   count (and (< (+ start i) (length output))
                                                             (eql (nth (+ start i) output)
                                                                  (nth i target-bits)))))))
                           population-list)))
        ;; Track best
        (loop for initial in population-list
              for score in scores
              when (> score best-score)
              do (setf best-score score
                       best-initial (copy-list initial)))

        ;; Report
        (when (zerop (mod gen 100))
          (format t "Gen ~4D: best = ~D/~D (~,1F%)~%"
                  gen best-score target-len
                  (* 100.0 (/ best-score target-len))))

        ;; Success?
        (when (= best-score target-len)
          (format t "~%*** PERFECT MATCH FOUND! ***~%")
          (return-from search-for-emergent-pattern
            (values best-initial best-score)))

        ;; Next generation via tournament + mutation
        (let ((new-pop (list best-initial)))
          (loop while (< (length new-pop) population)
                for p1 = (nth (random (length population-list)) population-list)
                for p2 = (nth (random (length population-list)) population-list)
                for s1 = (nth (random (length scores)) scores)
                for s2 = (nth (random (length scores)) scores)
                for parent = (if (> s1 s2) p1 p2)
                for child = (loop for bit in parent
                                 collect (if (< (random 1.0) 0.08) (- 1 bit) bit))
                do (push child new-pop))
          (setf population-list new-pop))))

    (values best-initial best-score)))

;; First, let's try to find just the lparen
(format t "~%~%=== PHASE 1: SEARCHING FOR EMERGENT '(' ===~%")
(multiple-value-bind (initial score)
    (search-for-emergent-pattern *lparen-bits*
                                 :ca-width 32
                                 :ca-generations 40
                                 :population 200
                                 :max-gens 1500)
  (if (= score 16)
      (progn
        (format t "~%SUCCESS! Found CA for '('~%")
        (format t "Initial: ~{~A~}~%" initial)
        ;; Verify
        (let* ((ca (rule110:make-ca-from-state (rule110:state-from-bits initial)))
               (final (rule110:run-ca ca 40)))
          (format t "Output:  ~{~A~}~%" (rule110:ca-to-bits final))))
      (format t "~%Best score: ~D/16 - need more exploration~%" score)))

(quit)
