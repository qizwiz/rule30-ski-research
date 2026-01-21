;;;; quine-search.lisp - Search for Rule 110 quines
;;;;
;;;; A quine is a fixed point: initial state I such that
;;;; after N generations, the CA outputs I again.
;;;;
;;;; This is the self-reproducing tiny AI.

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")

(defpackage :quine-search
  (:use :cl :rule110))

(in-package :quine-search)

(ensure-directories-exist "/Users/jonathanhill/src/rule110-claude/results/")

;;; ============================================================
;;; QUINE = FIXED POINT
;;; Find I such that run(CA(I), n) = I
;;; ============================================================

(defun is-quine-p (initial generations)
  "Check if initial state reproduces itself after N generations."
  (let* ((ca (make-ca-from-state (state-from-bits initial)))
         (final (run-ca ca generations))
         (output (coerce (ca-state final) 'list)))
    (equal initial output)))

(defun quine-distance (initial generations)
  "How close is this to being a quine? (0 = perfect quine)"
  (let* ((ca (make-ca-from-state (state-from-bits initial)))
         (final (run-ca ca generations))
         (output (coerce (ca-state final) 'list)))
    (loop for i in initial
          for o in output
          count (not (eql i o)))))

;;; ============================================================
;;; SEARCH FOR QUINES
;;; ============================================================

(defun search-for-quine (width generations &key (population 500) (max-gens 20000))
  "Search for a quine of given width."
  (format t "~%Searching for ~D-bit quine (CA generations: ~D)...~%~%" width generations)

  (let ((best-distance width)
        (best-initial nil)
        (pop (loop repeat population collect (loop repeat width collect (random 2))))
        (start-time (get-internal-real-time)))

    (dotimes (gen max-gens)
      ;; Evaluate
      (let ((distances (mapcar (lambda (i) (quine-distance i generations)) pop)))

        ;; Track best
        (loop for init in pop
              for dist in distances
              when (< dist best-distance)
              do (setf best-distance dist
                       best-initial (copy-list init)))

        ;; Check for quine
        (when (zerop best-distance)
          (format t "~%*** QUINE FOUND at generation ~D! ***~%" gen)
          (format t "Initial/Output: ~{~A~}~%" best-initial)
          (return-from search-for-quine (values best-initial t gen)))

        ;; Progress
        (when (zerop (mod gen 500))
          (let ((elapsed (/ (- (get-internal-real-time) start-time)
                           internal-time-units-per-second)))
            (format t "Gen ~5D: best distance = ~D/~D - ~,1Fs~%"
                    gen best-distance width elapsed)))

        ;; Next generation
        (let ((new-pop (list best-initial)))
          (loop while (< (length new-pop) population)
                for i1 = (random (length pop))
                for i2 = (random (length pop))
                for parent = (if (< (nth i1 distances) (nth i2 distances))
                                (nth i1 pop) (nth i2 pop))
                for child = (mapcar (lambda (b) (if (< (random 1.0) 0.1) (- 1 b) b)) parent)
                do (push child new-pop))
          (setf pop new-pop))))

    (format t "~%Best found: distance ~D~%" best-distance)
    (format t "Best initial: ~{~A~}~%" best-initial)
    (values best-initial nil best-distance)))

;;; ============================================================
;;; ALSO SEARCH FOR PERIOD-N CYCLES
;;; A period-2 cycle: I -> J -> I (also interesting)
;;; ============================================================

(defun find-cycle (initial max-period generations)
  "Find if initial state enters a cycle within max-period steps."
  (let ((states (list initial))
        (current initial))
    (dotimes (p max-period)
      (let* ((ca (make-ca-from-state (state-from-bits current)))
             (final (run-ca ca generations))
             (output (coerce (ca-state final) 'list)))
        (let ((pos (position output states :test #'equal)))
          (when pos
            (return-from find-cycle (values (- (length states) pos) pos))))
        (push output states)
        (setf current output)))
    nil))

;;; ============================================================
;;; MAIN
;;; ============================================================

(defun main ()
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║              RULE 110 QUINE SEARCH                            ║~%")
  (format t "║         Finding self-reproducing tiny AIs                     ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; Try different widths and generation counts
  ;; Smaller = more likely to find, but less interesting
  ;; Larger = harder to find, but more powerful

  ;; Start small: 8-bit quines
  (format t "~%~%=== SEARCHING FOR 8-BIT QUINES ===~%")
  (dolist (gens '(1 2 3 4 5 8 10))
    (format t "~%--- Trying ~D CA generations ---~%" gens)
    (multiple-value-bind (init found gen)
        (search-for-quine 8 gens :population 200 :max-gens 3000)
      (when found
        (format t "~%8-bit quine found for ~D generations!~%" gens)
        (with-open-file (out "/Users/jonathanhill/src/rule110-claude/results/quine-8bit.lisp"
                            :direction :output :if-exists :supersede)
          (format out ";;; 8-bit Rule 110 Quine~%")
          (format out ";;; Generations: ~D~%" gens)
          (format out "(~S~%" :quine-8bit)
          (format out " :initial-state ~S~%" init)
          (format out " :ca-generations ~D~%" gens)
          (format out " :type :fixed-point)~%"))
        (return))))

  ;; Try 16-bit
  (format t "~%~%=== SEARCHING FOR 16-BIT QUINES ===~%")
  (dolist (gens '(1 2 4 8 16))
    (format t "~%--- Trying ~D CA generations ---~%" gens)
    (multiple-value-bind (init found gen)
        (search-for-quine 16 gens :population 300 :max-gens 5000)
      (when found
        (format t "~%16-bit quine found!~%" gens)
        (with-open-file (out "/Users/jonathanhill/src/rule110-claude/results/quine-16bit.lisp"
                            :direction :output :if-exists :supersede)
          (format out ";;; 16-bit Rule 110 Quine~%")
          (format out ";;; Generations: ~D~%" gens)
          (format out "(~S~%" :quine-16bit)
          (format out " :initial-state ~S~%" init)
          (format out " :ca-generations ~D~%" gens)
          (format out " :type :fixed-point)~%"))
        (return))))

  ;; Try 32-bit (the real challenge)
  (format t "~%~%=== SEARCHING FOR 32-BIT QUINES ===~%")
  (multiple-value-bind (init found gen)
      (search-for-quine 32 16 :population 500 :max-gens 15000)
    (when found
      (format t "~%32-bit quine found!~%")
      (with-open-file (out "/Users/jonathanhill/src/rule110-claude/results/quine-32bit.lisp"
                          :direction :output :if-exists :supersede)
        (format out ";;; 32-bit Rule 110 Quine~%")
        (format out "(~S~%" :quine-32bit)
        (format out " :initial-state ~S~%" init)
        (format out " :ca-generations 16~%")
        (format out " :type :fixed-point)~%"))))

  (format t "~%~%========================================~%")
  (format t "QUINE SEARCH COMPLETE~%")
  (format t "Check results/ directory~%")
  (format t "========================================~%"))

(main)
(quit)
