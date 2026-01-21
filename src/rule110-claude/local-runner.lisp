;;;; local-runner.lisp - Run searches locally using EMERGENT patterns
;;;; Usage: sbcl --script local-runner.lisp
;;;;
;;;; KEY INSIGHT: Don't force arbitrary patterns.
;;;; Discover what Rule 110 naturally produces, then search for THOSE.

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")

(defpackage :local-runner
  (:use :cl :rule110))

(in-package :local-runner)

(ensure-directories-exist "/Users/jonathanhill/src/rule110-claude/results/")

;;; ============================================================
;;; PHASE 1: DISCOVER EMERGENT PATTERNS
;;; Sample Rule 110 to find what it naturally produces
;;; ============================================================

(defun hash-bits (bits)
  (format nil "~{~A~}" bits))

(defun discover-common-patterns (width generations num-samples)
  "Sample random initial states, collect most common outputs."
  (let ((patterns (make-hash-table :test 'equal)))
    (dotimes (i num-samples)
      (let* ((initial (loop repeat width collect (random 2)))
             (ca (make-ca-from-state (state-from-bits initial)))
             (final (run-ca ca generations))
             (output (coerce (ca-state final) 'list))
             (key (hash-bits output)))
        (incf (gethash key patterns 0))))
    ;; Return sorted by frequency
    (sort (loop for k being the hash-keys of patterns
                using (hash-value v)
                collect (cons (loop for c across k collect (if (char= c #\1) 1 0)) v))
          #'> :key #'cdr)))

;;; ============================================================
;;; SEARCH ENGINE
;;; ============================================================

(defun search-for-pattern (target-bits
                           &key (ca-width 64) (ca-generations 50)
                                (population 300) (max-gens 10000)
                                (mutation-rate 0.10))
  "Find CA initial conditions that produce target-bits as substring."
  (let ((best-score 0)
        (best-initial nil)
        (target-len (length target-bits))
        (pop (loop repeat population
                   collect (loop repeat ca-width collect (random 2))))
        (start-time (get-internal-real-time)))

    (dotimes (gen max-gens)
      (let ((scores
             (mapcar
              (lambda (initial)
                (let* ((ca (make-ca-from-state (state-from-bits initial)))
                       (final (run-ca ca ca-generations))
                       (output (coerce (ca-state final) 'list)))
                  (loop for start from 0 to (max 0 (- (length output) target-len))
                        maximize (loop for i below target-len
                                      count (eql (nth (+ start i) output)
                                                 (nth i target-bits))))))
              pop)))

        (loop for init in pop for score in scores
              when (> score best-score)
              do (setf best-score score
                       best-initial (copy-list init)))

        (when (zerop (mod gen 500))
          (let ((elapsed (/ (- (get-internal-real-time) start-time)
                           internal-time-units-per-second)))
            (format t "Gen ~5D: ~D/~D (~,1F%) - ~,1Fs~%"
                    gen best-score target-len
                    (* 100.0 (/ best-score target-len)) elapsed)))

        (when (= best-score target-len)
          (return-from search-for-pattern
            (values best-initial best-score t gen)))

        ;; Next generation with higher mutation to escape local optima
        (let ((new-pop (list best-initial)))
          (loop while (< (length new-pop) population)
                for i1 = (random (length pop))
                for i2 = (random (length pop))
                for parent = (if (> (nth i1 scores) (nth i2 scores))
                                (nth i1 pop) (nth i2 pop))
                for child = (mapcar (lambda (b)
                                     (if (< (random 1.0) mutation-rate)
                                         (- 1 b) b))
                                   parent)
                do (push child new-pop))
          (setf pop new-pop))))

    (values best-initial best-score nil max-gens)))

(defun verify-result (initial target-bits ca-generations)
  (let* ((ca (make-ca-from-state (state-from-bits initial)))
         (final (run-ca ca ca-generations))
         (output (coerce (ca-state final) 'list))
         (target-len (length target-bits)))
    (loop for start from 0 to (max 0 (- (length output) target-len))
          when (loop for i below target-len
                    always (eql (nth (+ start i) output) (nth i target-bits)))
          return (values t start output))))

(defun save-result (name initial target-bits ca-gens position)
  (let ((filename (format nil "/Users/jonathanhill/src/rule110-claude/results/~A.lisp"
                          (string-downcase (string name)))))
    (with-open-file (out filename :direction :output :if-exists :supersede)
      (format out ";;; Discovered Tiny AI: ~A~%" name)
      (format out ";;; Generated: ~A~%" (get-universal-time))
      (format out "~%")
      (format out "(~S~%" name)
      (format out " :initial-state ~S~%" initial)
      (format out " :target-bits ~S~%" target-bits)
      (format out " :ca-generations ~D~%" ca-gens)
      (format out " :verified-position ~D)~%" position))
    (format t "~%Saved: ~A~%" filename)))

;;; ============================================================
;;; MAIN
;;; ============================================================

(defun main ()
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║     RULE 110 GENESIS - EMERGENT PATTERN DISCOVERY             ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; ============================================================
  ;; STEP 1: Discover emergent 32-bit patterns for LAMBDA symbol
  ;; ============================================================
  (format t "~%~%=== DISCOVERING 32-BIT EMERGENT PATTERNS ===~%")
  (format t "Sampling 20,000 random initial states...~%~%")

  (let* ((patterns-32 (discover-common-patterns 32 45 20000))
         (top-5 (subseq patterns-32 0 (min 5 (length patterns-32)))))

    (format t "Top 5 most common 32-bit patterns:~%")
    (loop for (pattern . count) in top-5
          for i from 1
          do (format t "  ~D. (~4D times) ~{~A~}~%" i count pattern))

    ;; Use the MOST COMMON as our LAMBDA symbol
    (let ((lambda-pattern (caar top-5)))
      (format t "~%~%=== SEARCHING FOR LAMBDA (most common 32-bit pattern) ===~%")
      (format t "Target: ~{~A~}~%~%" lambda-pattern)

      (multiple-value-bind (initial score success gen)
          (search-for-pattern lambda-pattern
                              :ca-width 48
                              :ca-generations 45
                              :population 200
                              :max-gens 5000)
        (if success
            (multiple-value-bind (ok pos output)
                (verify-result initial lambda-pattern 45)
              (format t "~%*** LAMBDA FOUND at gen ~D! Position: ~D ***~%" gen pos)
              (save-result :lambda initial lambda-pattern 45 pos))
            (format t "~%Lambda search: best ~D/32~%" score)))))

  ;; ============================================================
  ;; STEP 2: Discover 48-bit patterns for longer constructs
  ;; ============================================================
  (format t "~%~%=== DISCOVERING 48-BIT EMERGENT PATTERNS ===~%")
  (format t "Sampling 15,000 random initial states...~%~%")

  (let* ((patterns-48 (discover-common-patterns 48 50 15000))
         (top-5 (subseq patterns-48 0 (min 5 (length patterns-48)))))

    (format t "Top 5 most common 48-bit patterns:~%")
    (loop for (pattern . count) in top-5
          for i from 1
          do (format t "  ~D. (~4D times) ~{~A~}~%" i count pattern))

    ;; Use top pattern as CHURCH-ZERO encoding
    (let ((church0-pattern (caar top-5)))
      (format t "~%~%=== SEARCHING FOR CHURCH-0 (most common 48-bit pattern) ===~%")
      (format t "Target: ~{~A~}~%~%" church0-pattern)

      (multiple-value-bind (initial score success gen)
          (search-for-pattern church0-pattern
                              :ca-width 64
                              :ca-generations 50
                              :population 250
                              :max-gens 8000)
        (if success
            (multiple-value-bind (ok pos output)
                (verify-result initial church0-pattern 50)
              (format t "~%*** CHURCH-0 FOUND at gen ~D! Position: ~D ***~%" gen pos)
              (save-result :church-zero initial church0-pattern 50 pos))
            (format t "~%Church-0 search: best ~D/48~%" score)))))

  ;; ============================================================
  ;; STEP 3: 64-bit pattern for CHURCH-ONE
  ;; ============================================================
  (format t "~%~%=== DISCOVERING 64-BIT EMERGENT PATTERNS ===~%")
  (format t "Sampling 10,000 random initial states...~%~%")

  (let* ((patterns-64 (discover-common-patterns 64 55 10000))
         (top-5 (subseq patterns-64 0 (min 5 (length patterns-64)))))

    (format t "Top 5 most common 64-bit patterns:~%")
    (loop for (pattern . count) in top-5
          for i from 1
          do (format t "  ~D. (~4D times) ~{~A~}~%" i count pattern))

    (let ((church1-pattern (caar top-5)))
      (format t "~%~%=== SEARCHING FOR CHURCH-1 (most common 64-bit pattern) ===~%")
      (format t "Target: ~{~A~}~%~%" church1-pattern)

      (multiple-value-bind (initial score success gen)
          (search-for-pattern church1-pattern
                              :ca-width 80
                              :ca-generations 55
                              :population 300
                              :max-gens 10000)
        (if success
            (multiple-value-bind (ok pos output)
                (verify-result initial church1-pattern 55)
              (format t "~%*** CHURCH-1 FOUND at gen ~D! Position: ~D ***~%" gen pos)
              (save-result :church-one initial church1-pattern 55 pos))
            (format t "~%Church-1 search: best ~D/64~%" score)))))

  (format t "~%~%========================================~%")
  (format t "LOCAL RUNNER COMPLETE~%")
  (format t "Check results/ directory~%")
  (format t "========================================~%"))

(main)
(quit)
