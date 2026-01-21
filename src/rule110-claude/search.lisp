;;;; search.lisp - Genetic search for CA initial conditions
;;;; The "tiny AI" that finds patterns producing target outputs
;;;;
;;;; This is the machine learning component:
;;;; Given a target string (e.g., "()" or "(lambda (x) x)")
;;;; Find initial conditions for Rule 110 that produce it

(defpackage :ca-search
  (:use :cl :rule110)
  (:export #:find-ca-for-target
           #:fitness
           #:target-to-bits
           #:*population-size*
           #:*generations*
           #:*mutation-rate*
           #:search-result
           #:search-result-initial-state
           #:search-result-ca
           #:search-result-fitness
           #:search-result-target
           #:search-result-generations-run))

(in-package :ca-search)

;;; Search parameters
(defvar *population-size* 100)
(defvar *generations* 1000)
(defvar *mutation-rate* 0.05)
(defvar *ca-run-generations* 50)  ; how many CA steps to run

;;; Result structure
(defstruct search-result
  initial-state      ; the winning initial condition
  ca                 ; final CA state
  fitness            ; how close to target
  target             ; what we were looking for
  generations-run)   ; CA generations executed

;;; Fitness function
(defun target-to-bits (target-string)
  "Convert target string to bit sequence."
  (let ((bits '()))
    (loop for char across target-string
          for code = (char-code char)
          do (loop for i from 7 downto 0
                   do (push (if (logbitp i code) 1 0) bits)))
    (nreverse bits)))

(defun hamming-distance (bits1 bits2)
  "Count differing bits between two sequences."
  (let ((len (min (length bits1) (length bits2))))
    (+ (loop for i below len
             count (not (eql (nth i bits1) (nth i bits2))))
       (abs (- (length bits1) (length bits2))))))

(defun substring-match-score (output-bits target-bits)
  "Score based on finding target as substring anywhere in output."
  (let ((out-len (length output-bits))
        (tgt-len (length target-bits))
        (best-score 0))
    (when (>= out-len tgt-len)
      (loop for start from 0 to (- out-len tgt-len)
            for window = (subseq output-bits start (+ start tgt-len))
            for matches = (loop for i below tgt-len
                               count (eql (nth i window) (nth i target-bits)))
            do (setf best-score (max best-score matches))))
    best-score))

(defun fitness (initial-state target-string ca-generations)
  "Evaluate fitness of an initial state for producing target.
   Higher is better. Perfect score = length of target in bits."
  (let* ((ca (make-ca-from-state (state-from-bits initial-state)))
         (final-ca (run-ca ca ca-generations))
         (output-bits (ca-to-bits final-ca))
         (target-bits (target-to-bits target-string)))
    (substring-match-score output-bits target-bits)))

;;; Genetic operators
(defun random-genome (length)
  "Create random initial state."
  (loop repeat length collect (random 2)))

(defun mutate (genome)
  "Mutate genome with probability *mutation-rate* per bit."
  (loop for bit in genome
        collect (if (< (random 1.0) *mutation-rate*)
                    (- 1 bit)
                    bit)))

(defun crossover (parent1 parent2)
  "Single-point crossover."
  (let ((point (random (length parent1))))
    (append (subseq parent1 0 point)
            (subseq parent2 point))))

(defun tournament-select (population fitnesses &optional (tournament-size 3))
  "Select individual via tournament selection."
  (let ((best-idx 0)
        (best-fit -1))
    (dotimes (i tournament-size)
      (let ((idx (random (length population))))
        (when (> (nth idx fitnesses) best-fit)
          (setf best-idx idx
                best-fit (nth idx fitnesses)))))
    (nth best-idx population)))

;;; Main search
(defun find-ca-for-target (target-string
                           &key
                           (ca-width 64)
                           (ca-generations *ca-run-generations*)
                           (population-size *population-size*)
                           (max-generations *generations*)
                           (verbose t))
  "Search for CA initial conditions that produce target string.
   Returns a SEARCH-RESULT on success."
  (let* ((target-bits (target-to-bits target-string))
         (perfect-score (length target-bits))
         (population (loop repeat population-size
                          collect (random-genome ca-width)))
         (best-ever nil)
         (best-ever-fitness 0))

    (when verbose
      (format t "~%=== SEARCHING FOR: ~S ===~%" target-string)
      (format t "Target bits: ~A~%" target-bits)
      (format t "Perfect score: ~D~%" perfect-score)
      (format t "CA width: ~D, CA generations: ~D~%" ca-width ca-generations)
      (format t "Population: ~D, Max generations: ~D~%~%"
              population-size max-generations))

    (dotimes (gen max-generations)
      ;; Evaluate fitness
      (let ((fitnesses (mapcar (lambda (genome)
                                (fitness genome target-string ca-generations))
                              population)))

        ;; Track best
        (loop for genome in population
              for fit in fitnesses
              when (> fit best-ever-fitness)
              do (setf best-ever genome
                       best-ever-fitness fit))

        ;; Report progress
        (when (and verbose (zerop (mod gen 50)))
          (format t "Gen ~4D: best=~D/~D (~,1F%)~%"
                  gen best-ever-fitness perfect-score
                  (* 100.0 (/ best-ever-fitness perfect-score))))

        ;; Check for success
        (when (= best-ever-fitness perfect-score)
          (when verbose
            (format t "~%*** FOUND PERFECT MATCH at generation ~D ***~%" gen))
          (let* ((final-ca (run-ca (make-ca-from-state (state-from-bits best-ever))
                                   ca-generations)))
            (return-from find-ca-for-target
              (make-search-result
               :initial-state best-ever
               :ca final-ca
               :fitness best-ever-fitness
               :target target-string
               :generations-run ca-generations))))

        ;; Create next generation
        (let ((new-pop (list best-ever)))  ; elitism
          (loop while (< (length new-pop) population-size)
                for parent1 = (tournament-select population fitnesses)
                for parent2 = (tournament-select population fitnesses)
                for child = (mutate (crossover parent1 parent2))
                do (push child new-pop))
          (setf population new-pop))))

    ;; Return best found even if not perfect
    (when verbose
      (format t "~%Search complete. Best: ~D/~D~%"
              best-ever-fitness perfect-score))
    (let* ((final-ca (run-ca (make-ca-from-state (state-from-bits best-ever))
                             ca-generations)))
      (make-search-result
       :initial-state best-ever
       :ca final-ca
       :fitness best-ever-fitness
       :target target-string
       :generations-run ca-generations))))

;;; Quick test
(defun test-search ()
  "Test searching for simple target."
  (find-ca-for-target "()"
                      :ca-width 32
                      :ca-generations 20
                      :population-size 50
                      :max-generations 200))
