;;;; tiny-ai.lisp - The foundational "tiny AI" abstraction
;;;; Each tiny AI is a CA with learned initial conditions
;;;; that produces a specific computational primitive
;;;;
;;;; This is where we BUILD UP lambda calculus from nothing

(defpackage :tiny-ai
  (:use :cl :rule110 :ca-search)
  (:export #:tiny-ai
           #:make-tiny-ai
           #:tiny-ai-name
           #:tiny-ai-output
           #:tiny-ai-initial-state
           #:tiny-ai-ca-generations
           #:tiny-ai-search-result
           #:run-tiny-ai
           #:compose-tiny-ais
           #:*registry*
           #:register-tiny-ai
           #:find-tiny-ai
           #:bootstrap-nil
           #:bootstrap-identity
           #:bootstrap-church-zero
           #:bootstrap-church-succ
           #:bootstrap-all
           #:bootstrap-primitive
           #:show-registry
           #:export-tiny-ai))

(in-package :tiny-ai)

;;; The Tiny AI structure
;;; Each one is a "learned" CA that produces a specific output
(defstruct tiny-ai
  name              ; human-readable name (e.g., "nil", "church-0")
  output            ; what this AI produces (e.g., "()")
  initial-state     ; the learned initial conditions
  ca-generations    ; how many generations to run
  search-result)    ; full search metadata

;;; Global registry of discovered tiny AIs
(defvar *registry* (make-hash-table :test 'equal))

(defun register-tiny-ai (ai)
  "Add a tiny AI to the global registry."
  (setf (gethash (tiny-ai-name ai) *registry*) ai)
  (format t "~%*** REGISTERED TINY AI: ~A ***~%" (tiny-ai-name ai))
  (format t "    Output: ~S~%" (tiny-ai-output ai))
  ai)

(defun find-tiny-ai (name)
  "Look up a tiny AI by name."
  (gethash name *registry*))

(defun show-registry ()
  "Display all registered tiny AIs."
  (format t "~%=== TINY AI REGISTRY ===~%")
  (maphash (lambda (name ai)
             (format t "  ~20A -> ~S~%" name (tiny-ai-output ai)))
           *registry*)
  (format t "========================~%"))

;;; Running a tiny AI
(defun run-tiny-ai (ai)
  "Execute the tiny AI and return its output."
  (let* ((ca (make-ca-from-state (state-from-bits (tiny-ai-initial-state ai))))
         (final-ca (run-ca ca (tiny-ai-ca-generations ai))))
    (ca-to-string final-ca)))

;;; Composition - this is key!
;;; When we have tiny AIs for A and B, we can compose them
(defun compose-tiny-ais (ai1 ai2 composition-type)
  "Compose two tiny AIs. This is where complexity emerges.
   composition-type can be :concat, :apply, :wrap"
  (let ((output1 (tiny-ai-output ai1))
        (output2 (tiny-ai-output ai2)))
    (case composition-type
      (:concat
       ;; Simple concatenation
       (concatenate 'string output1 output2))
      (:apply
       ;; Function application: (f x)
       (format nil "(~A ~A)" output1 output2))
      (:wrap
       ;; Wrap second in first: (first second)
       (format nil "(~A ~A)" output1 output2)))))

;;; Bootstrap functions - discover the fundamental tiny AIs

(defun bootstrap-primitive (name target &key (ca-width 64) (ca-generations 30)
                                            (population 200) (max-gens 2000))
  "Search for a tiny AI that produces the target output."
  (format t "~%~%========================================~%")
  (format t "BOOTSTRAPPING: ~A~%" name)
  (format t "TARGET: ~S~%" target)
  (format t "========================================~%")

  (let ((result (find-ca-for-target target
                                    :ca-width ca-width
                                    :ca-generations ca-generations
                                    :population-size population
                                    :max-generations max-gens)))
    (if (= (search-result-fitness result)
           (length (target-to-bits target)))
        ;; Success!
        (let ((ai (make-tiny-ai
                   :name name
                   :output target
                   :initial-state (search-result-initial-state result)
                   :ca-generations ca-generations
                   :search-result result)))
          (register-tiny-ai ai)
          ai)
        ;; Failed to find perfect match
        (progn
          (format t "~%!!! FAILED to find perfect match for ~A !!!~%" name)
          (format t "    Best fitness: ~D/~D~%"
                  (search-result-fitness result)
                  (length (target-to-bits target)))
          nil))))

;;; The fundamental primitives of Lisp/Lambda calculus

(defun bootstrap-nil ()
  "Find the tiny AI for NIL - the empty list ()"
  (bootstrap-primitive "nil" "()"
                       :ca-width 32
                       :ca-generations 20
                       :population 100
                       :max-gens 500))

(defun bootstrap-identity ()
  "Find the tiny AI for identity function"
  (bootstrap-primitive "identity" "(lambda (x) x)"
                       :ca-width 128
                       :ca-generations 40
                       :population 200
                       :max-gens 3000))

(defun bootstrap-church-zero ()
  "Find the tiny AI for Church numeral 0: (lambda (f) (lambda (x) x))"
  (bootstrap-primitive "church-0" "(lambda (f) (lambda (x) x))"
                       :ca-width 256
                       :ca-generations 50
                       :population 300
                       :max-gens 5000))

(defun bootstrap-church-succ ()
  "Find the tiny AI for Church SUCC function"
  (bootstrap-primitive "church-succ"
                       "(lambda (n) (lambda (f) (lambda (x) (f ((n f) x)))))"
                       :ca-width 512
                       :ca-generations 60
                       :population 500
                       :max-gens 10000))

;;; Derived primitives through composition

(defun derive-church-one ()
  "Once we have church-0 and church-succ, derive church-1"
  (let ((zero (find-tiny-ai "church-0"))
        (succ (find-tiny-ai "church-succ")))
    (when (and zero succ)
      ;; Church 1 = (succ 0)
      ;; We can either:
      ;; 1. Search for it directly
      ;; 2. Compose existing tiny AIs
      ;; For now, let's search but with the hint of composition
      (bootstrap-primitive "church-1"
                          "(lambda (f) (lambda (x) (f x)))"
                          :ca-width 200
                          :ca-generations 45
                          :population 300
                          :max-gens 5000))))

;;; The grand experiment
(defun bootstrap-all ()
  "Attempt to bootstrap all fundamental primitives."
  (format t "~%~%")
  (format t "╔════════════════════════════════════════════════════════╗~%")
  (format t "║     RULE 110 LISP GENESIS - BOOTSTRAP SEQUENCE         ║~%")
  (format t "║     Building Lambda Calculus from Cellular Automata    ║~%")
  (format t "╚════════════════════════════════════════════════════════╝~%")

  ;; Start with the simplest
  (bootstrap-nil)

  ;; Build up
  (when (find-tiny-ai "nil")
    (bootstrap-identity))

  (when (find-tiny-ai "identity")
    (bootstrap-church-zero))

  (when (find-tiny-ai "church-0")
    (bootstrap-church-succ))

  (when (find-tiny-ai "church-succ")
    (derive-church-one))

  ;; Report
  (format t "~%~%")
  (format t "╔════════════════════════════════════════════════════════╗~%")
  (format t "║                 BOOTSTRAP COMPLETE                      ║~%")
  (format t "╚════════════════════════════════════════════════════════╝~%")
  (show-registry))

;;; Helper to export a tiny AI as pure data
(defun export-tiny-ai (ai)
  "Export a tiny AI as a portable s-expression."
  `(:tiny-ai
    :name ,(tiny-ai-name ai)
    :output ,(tiny-ai-output ai)
    :initial-state ,(tiny-ai-initial-state ai)
    :ca-generations ,(tiny-ai-ca-generations ai)))
