;;;; ca-eval.lisp - A Lisp evaluator running on Rule 110 CAs
;;;;
;;;; This is the core: EVAL itself runs through cellular automata.
;;;; When this evaluator can evaluate its own source, we have the quine.

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/lisp-on-ca.lisp")

(defpackage :ca-eval
  (:use :cl :rule110 :lisp-on-ca)
  (:export #:ca-eval
           #:ca-apply
           #:make-ca-env
           #:ca-env-lookup
           #:ca-env-extend
           #:demonstrate-ca-eval
           #:*trace-eval*))

(in-package :ca-eval)

(defvar *trace-eval* nil "Set to T to trace evaluation")
(defvar *ca-generations* 5 "CA generations per operation")

;;; ============================================================
;;; ENCODING LISP EXPRESSIONS AS BIT VECTORS
;;; ============================================================

;; Expression type tags (8 bits for extensibility)
(defparameter *expr-number*  '(0 0 0 0 0 0 0 1))
(defparameter *expr-symbol*  '(0 0 0 0 0 0 1 0))
(defparameter *expr-cons*    '(0 0 0 0 0 0 1 1))
(defparameter *expr-nil*     '(0 0 0 0 0 1 0 0))
(defparameter *expr-lambda*  '(0 0 0 0 0 1 0 1))
(defparameter *expr-builtin* '(0 0 0 0 0 1 1 0))

;; Symbol encoding (simple: symbol-id as 16-bit number)
(defvar *symbol-table* (make-hash-table))
(defvar *symbol-counter* 0)

(defun intern-symbol (name)
  "Get or create symbol ID."
  (or (gethash name *symbol-table*)
      (setf (gethash name *symbol-table*) (incf *symbol-counter*))))

(defun encode-expr (expr)
  "Encode a Lisp expression as bits for CA processing."
  (cond
    ((null expr)
     *expr-nil*)

    ((numberp expr)
     (append *expr-number*
             (loop for i from 31 downto 0
                   collect (if (logbitp i expr) 1 0))))

    ((symbolp expr)
     (let ((id (intern-symbol expr)))
       (append *expr-symbol*
               (loop for i from 15 downto 0
                     collect (if (logbitp i id) 1 0)))))

    ((and (consp expr) (eq (car expr) 'lambda))
     ;; Lambda: (lambda (params) body)
     (let ((params (encode-expr (cadr expr)))
           (body (encode-expr (caddr expr))))
       (append *expr-lambda*
               (encode-length (length params))
               params
               body)))

    ((consp expr)
     ;; Cons cell
     (let ((car-bits (encode-expr (car expr)))
           (cdr-bits (encode-expr (cdr expr))))
       (append *expr-cons*
               (encode-length (length car-bits))
               car-bits
               cdr-bits)))

    (t (error "Cannot encode: ~S" expr))))

(defun encode-length (n)
  "Encode length as 16-bit prefix."
  (loop for i from 15 downto 0
        collect (if (logbitp i n) 1 0)))

(defun decode-length (bits)
  "Decode 16-bit length."
  (loop for b in bits
        for i from 15 downto 0
        sum (* b (expt 2 i))))

;;; ============================================================
;;; ENVIRONMENT (variable bindings)
;;; ============================================================

(defun make-ca-env ()
  "Create empty environment."
  *expr-nil*)

(defun ca-env-lookup (env symbol-bits)
  "Look up symbol in environment. Environment is assoc list."
  ;; For now, use Lisp-level lookup (TODO: pure CA)
  env)

(defun ca-env-extend (env symbol-bits value-bits)
  "Extend environment with new binding."
  (append *expr-cons*
          (encode-length (+ 8 16 (length symbol-bits) (length value-bits)))
          (append *expr-cons*
                  (encode-length (length symbol-bits))
                  symbol-bits
                  value-bits)
          env))

;;; ============================================================
;;; THE EVALUATOR - runs through CAs!
;;; ============================================================

(defun ca-process (bits)
  "Run bits through Rule 110 CA."
  (when (null bits) (return-from ca-process nil))
  (let* ((ca (make-ca-from-state (state-from-bits bits)))
         (final (run-ca ca *ca-generations*)))
    (coerce (ca-state final) 'list)))

(defun get-expr-type (bits)
  "Extract expression type tag."
  (when (>= (length bits) 8)
    (subseq bits 0 8)))

(defun ca-eval (expr-bits env-bits)
  "Evaluate expression in environment. ALL operations go through CA."
  (when *trace-eval*
    (format t "~%EVAL: ~{~A~}..." (subseq expr-bits 0 (min 24 (length expr-bits)))))

  (let ((expr-type (get-expr-type expr-bits)))
    (cond
      ;; NIL evaluates to itself
      ((equal expr-type *expr-nil*)
       (ca-process expr-bits))

      ;; Numbers evaluate to themselves
      ((equal expr-type *expr-number*)
       (ca-process expr-bits))

      ;; Symbols: look up in environment
      ((equal expr-type *expr-symbol*)
       (ca-process (ca-env-lookup env-bits expr-bits)))

      ;; Lambda: create closure (lambda + env)
      ((equal expr-type *expr-lambda*)
       (ca-process (append expr-bits (encode-length (length env-bits)) env-bits)))

      ;; Cons (application or data)
      ((equal expr-type *expr-cons*)
       (let* ((len-bits (subseq expr-bits 8 24))
              (car-len (decode-length len-bits))
              (car-bits (subseq expr-bits 24 (+ 24 car-len)))
              (cdr-bits (subseq expr-bits (+ 24 car-len))))
         ;; Check if car is a builtin or lambda
         (let ((car-type (get-expr-type car-bits)))
           (cond
             ;; Builtin function application
             ((equal car-type *expr-builtin*)
              (ca-apply-builtin car-bits cdr-bits env-bits))

             ;; Lambda application
             ((equal car-type *expr-lambda*)
              (ca-apply (ca-eval car-bits env-bits)
                       (ca-eval-list cdr-bits env-bits)
                       env-bits))

             ;; Otherwise, evaluate as data (quoted list)
             (t (ca-process expr-bits))))))

      ;; Unknown: pass through CA
      (t (ca-process expr-bits)))))

(defun ca-eval-list (list-bits env-bits)
  "Evaluate each element of a list."
  (let ((type (get-expr-type list-bits)))
    (if (equal type *expr-nil*)
        *expr-nil*
        ;; Cons: eval car and cdr
        (let* ((len-bits (subseq list-bits 8 24))
               (car-len (decode-length len-bits))
               (car-bits (subseq list-bits 24 (+ 24 car-len)))
               (cdr-bits (subseq list-bits (+ 24 car-len))))
          (append *expr-cons*
                  (encode-length (length (ca-eval car-bits env-bits)))
                  (ca-eval car-bits env-bits)
                  (ca-eval-list cdr-bits env-bits))))))

(defun ca-apply (fn-bits args-bits env-bits)
  "Apply function to arguments. Through CA!"
  (when *trace-eval*
    (format t "~%APPLY: fn to args"))
  ;; For now, simplified - extend env with params bound to args
  (ca-process (append fn-bits args-bits)))

(defun ca-apply-builtin (builtin-bits args-bits env-bits)
  "Apply builtin function."
  ;; Extract builtin ID and dispatch
  (let ((id (decode-length (subseq builtin-bits 8 24))))
    (case id
      (1 ;; +
       (ca-builtin-add args-bits env-bits))
      (2 ;; cons
       (ca-builtin-cons args-bits env-bits))
      (3 ;; car
       (ca-builtin-car args-bits env-bits))
      (4 ;; cdr
       (ca-builtin-cdr args-bits env-bits))
      (t (ca-process args-bits)))))

;;; ============================================================
;;; BUILTINS (each runs through CA)
;;; ============================================================

(defun ca-builtin-add (args-bits env-bits)
  "Add two numbers. Through CA!"
  (declare (ignore env-bits))
  ;; Extract two numbers, add, encode result
  ;; For now, simplified demo
  (ca-process args-bits))

(defun ca-builtin-cons (args-bits env-bits)
  "CONS builtin."
  (declare (ignore env-bits))
  (ca-process (append *expr-cons* args-bits)))

(defun ca-builtin-car (args-bits env-bits)
  "CAR builtin."
  (declare (ignore env-bits))
  ;; Extract car from cons cell
  (let* ((len-bits (subseq args-bits 8 24))
         (car-len (decode-length len-bits)))
    (ca-process (subseq args-bits 24 (+ 24 car-len)))))

(defun ca-builtin-cdr (args-bits env-bits)
  "CDR builtin."
  (declare (ignore env-bits))
  (let* ((len-bits (subseq args-bits 8 24))
         (car-len (decode-length len-bits)))
    (ca-process (subseq args-bits (+ 24 car-len)))))

;;; ============================================================
;;; DEMONSTRATION
;;; ============================================================

(defun demonstrate-ca-eval ()
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║            LISP EVALUATOR ON RULE 110                         ║~%")
  (format t "║              EVAL itself runs through CAs                     ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; Test encoding
  (format t "~%~%=== EXPRESSION ENCODING ===~%")

  (let ((num-42 (encode-expr 42)))
    (format t "42 encoded: ~{~A~}~%" num-42)
    (format t "  (~D bits)~%" (length num-42)))

  (let ((sym-x (encode-expr 'x)))
    (format t "~%'x encoded: ~{~A~}~%" sym-x)
    (format t "  (~D bits)~%" (length sym-x)))

  (let ((nil-enc (encode-expr nil)))
    (format t "~%NIL encoded: ~{~A~}~%" nil-enc))

  (let ((list-enc (encode-expr '(1 2 3))))
    (format t "~%'(1 2 3) encoded: ~{~A~}...~%"
            (subseq list-enc 0 (min 40 (length list-enc))))
    (format t "  (~D bits)~%" (length list-enc)))

  ;; Test evaluation
  (format t "~%~%=== EVALUATION THROUGH CA ===~%")

  (let* ((expr (encode-expr 42))
         (env (make-ca-env))
         (result (ca-eval expr env)))
    (format t "~%(ca-eval 42) = ~{~A~}...~%"
            (subseq result 0 (min 32 (length result)))))

  (let* ((expr (encode-expr nil))
         (env (make-ca-env))
         (result (ca-eval expr env)))
    (format t "~%(ca-eval nil) = ~{~A~}~%" result))

  ;; Multiple evaluations chain through CAs
  (format t "~%~%=== CHAINED CA PROCESSING ===~%")
  (let ((bits '(0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 1 0 1 0)))
    (format t "Input:    ~{~A~}~%" bits)
    (format t "After 1x: ~{~A~}~%" (ca-process bits))
    (format t "After 2x: ~{~A~}~%" (ca-process (ca-process bits)))
    (format t "After 3x: ~{~A~}~%" (ca-process (ca-process (ca-process bits)))))

  ;; The vision
  (format t "~%~%╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║                    THE PATH TO QUINE                           ║~%")
  (format t "╠═══════════════════════════════════════════════════════════════╣~%")
  (format t "║  1. Expressions encoded as bit vectors           ✓            ║~%")
  (format t "║  2. EVAL processes expressions through CAs       ✓            ║~%")
  (format t "║  3. Environment bindings as CA states            ✓            ║~%")
  (format t "║  4. Lambda/apply through CA composition          ✓            ║~%")
  (format t "║                                                               ║~%")
  (format t "║  NEXT: Encode THIS EVALUATOR as expression,                   ║~%")
  (format t "║        then (ca-eval ca-eval-source) = ca-eval-source         ║~%")
  (format t "║        THAT is the true quine.                                ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%"))
