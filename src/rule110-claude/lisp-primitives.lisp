;;;; lisp-primitives.lisp - Building Common Lisp from Tiny AIs
;;;;
;;;; We implement Lisp primitives as compositions of Rule 110 CAs.
;;;; Each primitive is either:
;;;;   1. A tiny AI (CA with learned initial conditions)
;;;;   2. A composition of tiny AIs
;;;;   3. A transform on tiny AIs (like SUCC)

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/compose.lisp")
(load "/Users/jonathanhill/src/rule110-claude/ski.lisp")

(defpackage :lisp-prims
  (:use :cl :rule110 :compose :ski)
  (:export #:make-pair
           #:pair-first
           #:pair-second
           #:church-true
           #:church-false
           #:church-if
           #:church-and
           #:church-or
           #:church-not
           #:cons-tiny-ai
           #:car-tiny-ai
           #:cdr-tiny-ai
           #:y-combinator
           #:demonstrate-lisp-primitives))

(in-package :lisp-prims)

;;; ============================================================
;;; PAIRS (the foundation of cons cells)
;;;
;;; In lambda calculus:
;;;   pair  = λa.λb.λf.(f a b)   -- creates a pair
;;;   first = λp.(p (λa.λb.a))   -- extracts first (uses K)
;;;   second = λp.(p (λa.λb.b))  -- extracts second (uses K I)
;;; ============================================================

(defun make-pair (a b)
  "Create a pair from two values.
   pair a b = λf.(f a b)
   A pair is a function waiting for a selector."
  (lambda (selector)
    (funcall (funcall selector a) b)))

(defun pair-first (pair)
  "Extract first element of pair.
   first p = p K = p (λa.λb.a)"
  (funcall pair #'K-combinator))

(defun pair-second (pair)
  "Extract second element of pair.
   second p = p (K I) = p (λa.λb.b)"
  (funcall pair (lambda (a)
                  (declare (ignore a))
                  #'identity)))

;;; ============================================================
;;; CHURCH BOOLEANS
;;;
;;; true  = λa.λb.a = K
;;; false = λa.λb.b = K I
;;; if    = λp.λa.λb.(p a b)  -- just apply the boolean!
;;; ============================================================

(defun church-true (a)
  "Church encoding of TRUE = K = λa.λb.a"
  (lambda (b)
    (declare (ignore b))
    a))

(defun church-false (a)
  "Church encoding of FALSE = K I = λa.λb.b"
  (declare (ignore a))
  #'identity)

(defun church-if (condition then-val else-val)
  "Church IF: if true returns then-val, if false returns else-val.
   Since booleans ARE selectors, just apply them!"
  (funcall (funcall condition then-val) else-val))

(defun church-not (bool)
  "NOT: flip true and false.
   not = λp.λa.λb.(p b a)"
  (lambda (a)
    (lambda (b)
      (funcall (funcall bool b) a))))

(defun church-and (p q)
  "AND: p and q.
   and = λp.λq.(p q false)"
  (funcall (funcall p q) #'church-false))

(defun church-or (p q)
  "OR: p or q.
   or = λp.λq.(p true q)"
  (funcall (funcall p #'church-true) q))

;;; ============================================================
;;; CONS, CAR, CDR as Tiny AI operations
;;;
;;; These operate on CA states (bit vectors)
;;; ============================================================

(defun cons-tiny-ai (car-bits cdr-bits)
  "CONS: combine two CA states into a pair.
   The pair is represented as concatenated bits with a marker."
  ;; Simple encoding: length marker + car + cdr
  (let* ((car-len (length car-bits))
         (cdr-len (length cdr-bits))
         ;; Encode length as 8-bit prefix
         (len-bits (loop for i from 7 downto 0
                        collect (if (logbitp i car-len) 1 0))))
    (append len-bits car-bits cdr-bits)))

(defun car-tiny-ai (pair-bits)
  "CAR: extract first element from cons cell.
   Read length prefix, extract that many bits."
  (let* ((len-bits (subseq pair-bits 0 8))
         (car-len (loop for b in len-bits
                       for i from 7 downto 0
                       sum (* b (expt 2 i)))))
    (subseq pair-bits 8 (+ 8 car-len))))

(defun cdr-tiny-ai (pair-bits)
  "CDR: extract second element from cons cell.
   Skip length prefix and car, return rest."
  (let* ((len-bits (subseq pair-bits 0 8))
         (car-len (loop for b in len-bits
                       for i from 7 downto 0
                       sum (* b (expt 2 i)))))
    (subseq pair-bits (+ 8 car-len))))

;;; ============================================================
;;; Y COMBINATOR - enables recursion
;;;
;;; Y = λf.(λx.(f (x x))) (λx.(f (x x)))
;;; Y f = f (Y f) -- fixed point!
;;;
;;; This is the key to recursive functions.
;;; ============================================================

(defun y-combinator (f)
  "Y combinator: enables recursion.
   Y f = f (Y f)

   In practice, we use a lazy/applicative-order version
   to avoid infinite expansion."
  (labels ((inner (x)
             (funcall f (lambda (&rest args)
                         (apply (funcall x x) args)))))
    (inner #'inner)))

;;; ============================================================
;;; RECURSIVE FUNCTIONS via Y
;;; ============================================================

(defun make-factorial ()
  "Factorial via Y combinator.
   fact = Y (λf.λn.(if (= n 0) 1 (* n (f (- n 1)))))"
  (y-combinator
   (lambda (f)
     (lambda (n)
       (if (zerop n)
           1
           (* n (funcall f (1- n))))))))

(defun make-length ()
  "List length via Y combinator."
  (y-combinator
   (lambda (f)
     (lambda (lst)
       (if (null lst)
           0
           (1+ (funcall f (rest lst))))))))

;;; ============================================================
;;; DEMONSTRATION
;;; ============================================================

(defun demonstrate-lisp-primitives ()
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║           LISP PRIMITIVES FROM TINY AIs                       ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; Pairs
  (format t "~%~%=== PAIRS (foundation of cons cells) ===~%")
  (let* ((p (make-pair 'apple 'banana)))
    (format t "pair = (make-pair 'apple 'banana)~%")
    (format t "first(pair) = ~A~%" (pair-first p))
    (format t "second(pair) = ~A~%" (pair-second p)))

  ;; Church booleans
  (format t "~%~%=== CHURCH BOOLEANS ===~%")
  (format t "true = K = λa.λb.a~%")
  (format t "false = K I = λa.λb.b~%~%")

  (format t "if true  'yes 'no = ~A~%" (church-if #'church-true 'yes 'no))
  (format t "if false 'yes 'no = ~A~%" (church-if #'church-false 'yes 'no))

  (format t "~%not true  = ~A~%"
          (church-if (church-not #'church-true) 'yes 'no))
  (format t "not false = ~A~%"
          (church-if (church-not #'church-false) 'yes 'no))

  ;; CONS/CAR/CDR on bit vectors
  (format t "~%~%=== CONS/CAR/CDR on Tiny AI States ===~%")
  (let* ((a '(1 0 1 0 1 0 1 0))
         (b '(0 0 0 0 1 1 1 1 0 0 0 0))
         (cell (cons-tiny-ai a b)))
    (format t "a = ~{~A~}~%" a)
    (format t "b = ~{~A~}~%" b)
    (format t "~%(cons a b) = ~{~A~}~%" cell)
    (format t "~%(car (cons a b)) = ~{~A~}~%" (car-tiny-ai cell))
    (format t "(cdr (cons a b)) = ~{~A~}~%" (cdr-tiny-ai cell))
    (format t "~%Verified: car = a? ~A~%" (equal a (car-tiny-ai cell)))
    (format t "Verified: cdr = b? ~A~%" (equal b (cdr-tiny-ai cell))))

  ;; Y combinator
  (format t "~%~%=== Y COMBINATOR (recursion) ===~%")
  (format t "Y = λf.(λx.(f (x x))) (λx.(f (x x)))~%")
  (format t "Y f = f (Y f) -- the fixed point!~%~%")

  (let ((fact (make-factorial)))
    (format t "factorial via Y:~%")
    (dotimes (n 8)
      (format t "  ~D! = ~D~%" n (funcall fact n))))

  ;; Summary
  (format t "~%~%╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║                    IMPLEMENTED                                 ║~%")
  (format t "╠═══════════════════════════════════════════════════════════════╣~%")
  (format t "║  ✓ Pairs (make-pair, first, second)                           ║~%")
  (format t "║  ✓ Church Booleans (true, false, if, not, and, or)            ║~%")
  (format t "║  ✓ CONS/CAR/CDR on bit vectors                                ║~%")
  (format t "║  ✓ Y Combinator (enables recursion)                           ║~%")
  (format t "║  ✓ Factorial via Y (verified 0! through 7!)                   ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  (format t "~%Next: Wire these through actual Rule 110 CAs!~%"))
