;;;; compose.lisp - Composition layer for Tiny AIs
;;;; This is where "produces patterns" becomes "computes"
;;;;
;;;; KEY INSIGHT: The output of one CA becomes the input of another.
;;;; This is how we wire tiny AIs into circuits.

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/registry.lisp")

(defpackage :compose
  (:use :cl :rule110 :genesis-registry)
  (:export #:wire
           #:compose-sequential
           #:compose-parallel
           #:make-circuit
           #:run-circuit
           #:demonstrate-composition))

(in-package :compose)

;;; ============================================================
;;; CORE COMPOSITION PRIMITIVE
;;; ============================================================

(defun wire (ca1-output ca2-width &key (offset 0) (wrap t))
  "Wire output of CA1 to input of CA2.
   offset: where in CA1's output to start reading
   wrap: if CA1 output is shorter, wrap around
   Returns: initial state for CA2"
  (let* ((out-len (length ca1-output))
         (result (make-list ca2-width :initial-element 0)))
    (dotimes (i ca2-width)
      (let ((src-idx (mod (+ offset i) out-len)))
        (setf (nth i result) (nth src-idx ca1-output))))
    result))

;;; ============================================================
;;; SEQUENTIAL COMPOSITION: CA1 → CA2 → CA3 → ...
;;; ============================================================

(defstruct tiny-ai-spec
  name
  initial-state      ; can be :from-previous or a bit list
  ca-generations
  output-offset      ; where to read output from
  output-width)      ; how many bits to take

(defun run-tiny-ai-with-input (spec input-bits)
  "Run a tiny AI with given input bits as initial state."
  (let* ((initial (if (eq (tiny-ai-spec-initial-state spec) :from-previous)
                      input-bits
                      (tiny-ai-spec-initial-state spec)))
         (ca (make-ca-from-state (state-from-bits initial)))
         (final (run-ca ca (tiny-ai-spec-ca-generations spec)))
         (output (coerce (ca-state final) 'list)))
    ;; Extract the relevant portion of output
    (if (tiny-ai-spec-output-width spec)
        (let ((off (or (tiny-ai-spec-output-offset spec) 0))
              (width (tiny-ai-spec-output-width spec)))
          (subseq output off (min (+ off width) (length output))))
        output)))

(defun compose-sequential (specs &optional initial-input)
  "Compose multiple tiny AIs sequentially.
   Output of each feeds into next."
  (let ((current-output initial-input))
    (dolist (spec specs)
      (setf current-output
            (run-tiny-ai-with-input spec current-output)))
    current-output))

;;; ============================================================
;;; CHURCH NUMERAL OPERATIONS
;;; ============================================================

;;; Church numerals are functions: they take f and x, apply f n times to x
;;; In CA terms:
;;; - Church 0: output = x (ignore f)
;;; - Church 1: output = f(x) = run f-CA with x as input
;;; - Church n: output = f(f(...f(x)...)) = run f-CA n times

(defun church-apply (n f-tiny-ai x-bits)
  "Apply Church numeral n: run f-tiny-ai n times on x-bits.
   This IS what a Church numeral computes."
  (let ((current x-bits))
    (dotimes (i n)
      (let* ((ca (make-ca-from-state (state-from-bits current)))
             (final (run-ca ca (getf f-tiny-ai :generations 40)))
             (output (coerce (ca-state final) 'list)))
        (setf current output)))
    current))

(defun make-succ-transform ()
  "SUCC takes a Church numeral and returns the next one.
   In CA terms: SUCC(n) produces a circuit that applies f one more time.

   But here's the key insight: we don't need to FIND a CA for SUCC.
   SUCC is a META-operation: it transforms tiny AIs into other tiny AIs.

   SUCC(church-n) = a new tiny AI that runs f one more time than church-n did."
  (lambda (church-n-apply-fn)
    ;; Returns a new function that applies f one more time
    (lambda (f-tiny-ai x-bits)
      (let ((result (funcall church-n-apply-fn f-tiny-ai x-bits)))
        ;; Apply f one more time
        (let* ((ca (make-ca-from-state (state-from-bits result)))
               (final (run-ca ca (getf f-tiny-ai :generations 40))))
          (coerce (ca-state final) 'list))))))

;;; ============================================================
;;; DEMONSTRATION
;;; ============================================================

(defun demonstrate-composition ()
  "Show that composition actually works."
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║          TINY AI COMPOSITION DEMONSTRATION                    ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; Demo 1: Basic wiring
  (format t "~%~%=== DEMO 1: Basic Wiring ===~%")
  (format t "Wire output of one CA to input of another.~%~%")

  (let* ((initial-1 '(1 0 1 0 1 0 1 0 1 0 1 0 1 0 1 0))  ; 16 bits
         (ca1 (make-ca-from-state (state-from-bits initial-1)))
         (final-1 (run-ca ca1 20))
         (output-1 (coerce (ca-state final-1) 'list)))
    (format t "CA1 initial: ~{~A~}~%" initial-1)
    (format t "CA1 output:  ~{~A~}~%" output-1)

    ;; Wire CA1 output to CA2 input
    (let* ((ca2-input (wire output-1 16))
           (ca2 (make-ca-from-state (state-from-bits ca2-input)))
           (final-2 (run-ca ca2 20))
           (output-2 (coerce (ca-state final-2) 'list)))
      (format t "~%CA2 input (from CA1): ~{~A~}~%" ca2-input)
      (format t "CA2 output:           ~{~A~}~%" output-2)
      (format t "~%Composition: CA1 → CA2 complete!~%")))

  ;; Demo 2: Church numeral behavior
  (format t "~%~%=== DEMO 2: Church Numeral Behavior ===~%")
  (format t "Church n applies function f exactly n times.~%~%")

  ;; Define a simple "increment" CA that shifts bits left
  (let ((x-bits '(0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)))  ; represents "1" position
    (format t "Starting x: ~{~A~}~%" x-bits)

    ;; Church 0: apply f zero times (return x unchanged conceptually)
    (format t "~%Church 0 (apply f 0 times):~%")
    (let ((result-0 (church-apply 0 '(:generations 15) x-bits)))
      (format t "  Result: ~{~A~}~%" result-0))

    ;; Church 1: apply f once
    (format t "~%Church 1 (apply f 1 time):~%")
    (let ((result-1 (church-apply 1 '(:generations 15) x-bits)))
      (format t "  Result: ~{~A~}~%" result-1))

    ;; Church 2: apply f twice
    (format t "~%Church 2 (apply f 2 times):~%")
    (let ((result-2 (church-apply 2 '(:generations 15) x-bits)))
      (format t "  Result: ~{~A~}~%" result-2))

    ;; Church 3: apply f three times
    (format t "~%Church 3 (apply f 3 times):~%")
    (let ((result-3 (church-apply 3 '(:generations 15) x-bits)))
      (format t "  Result: ~{~A~}~%" result-3)))

  ;; Demo 3: SUCC operation
  (format t "~%~%=== DEMO 3: SUCC Operation ===~%")
  (format t "SUCC transforms Church n into Church (n+1).~%")
  (format t "This is a META-operation on tiny AIs.~%~%")

  (let* ((church-0 (lambda (f x) (church-apply 0 f x)))
         (succ (make-succ-transform))
         (church-1 (funcall succ church-0))
         (church-2 (funcall succ church-1))
         (x-bits '(0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0))
         (f '(:generations 15)))

    (format t "church-0(f, x) = ~{~A~}~%" (funcall church-0 f x-bits))
    (format t "SUCC(church-0)(f, x) = church-1(f, x) = ~{~A~}~%"
            (funcall church-1 f x-bits))
    (format t "SUCC(SUCC(church-0))(f, x) = church-2(f, x) = ~{~A~}~%"
            (funcall church-2 f x-bits)))

  (format t "~%~%=== KEY INSIGHT ===~%")
  (format t "SUCC doesn't need its own CA - it's a TRANSFORM on CAs.~%")
  (format t "Church numerals ARE the composition: 'run f n times'.~%")
  (format t "The 'compiler' (SUCC, combinators) operates on tiny AIs themselves.~%")

  (format t "~%~%=== NEXT STEP: Replace Bootstrap ===~%")
  (format t "Once we have S, K, I combinators as transforms on tiny AIs,~%")
  (format t "ANY computable function can be built from composition.~%")
  (format t "Then the bootstrap Lisp becomes just the first layer.~%"))
