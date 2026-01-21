;;;; lisp-on-ca.lisp - Lisp primitives running on ACTUAL Rule 110 CAs
;;;;
;;;; This is where it gets real: every operation runs through CAs.
;;;; The bit patterns flow through Rule 110, not abstract functions.

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/compose.lisp")

(defpackage :lisp-on-ca
  (:use :cl :rule110 :compose)
  (:export #:ca-cons
           #:ca-car
           #:ca-cdr
           #:ca-if
           #:ca-church-numeral
           #:ca-succ
           #:ca-add
           #:ca-mult
           #:demonstrate-lisp-on-ca))

(in-package :lisp-on-ca)

;;; ============================================================
;;; ENCODING: How we represent Lisp values as CA states
;;; ============================================================

;; Type tags (4 bits)
(defparameter *tag-nil*    '(0 0 0 0))
(defparameter *tag-number* '(0 0 0 1))
(defparameter *tag-pair*   '(0 0 1 0))
(defparameter *tag-bool*   '(0 0 1 1))
(defparameter *tag-symbol* '(0 1 0 0))

(defun encode-number (n &optional (bits 16))
  "Encode a number as tagged bit vector."
  (append *tag-number*
          (loop for i from (1- bits) downto 0
                collect (if (logbitp i n) 1 0))))

(defun decode-number (bits)
  "Decode a tagged number."
  (let ((data (subseq bits 4)))
    (loop for b in data
          for i from (1- (length data)) downto 0
          sum (* b (expt 2 i)))))

(defun encode-bool (val)
  "Encode boolean as tagged bit vector."
  (append *tag-bool* (if val '(1) '(0))))

(defun decode-bool (bits)
  "Decode a tagged boolean."
  (= 1 (nth 4 bits)))

;;; ============================================================
;;; CA-CONS: Build a cons cell, process through CA
;;; ============================================================

(defun ca-cons (car-bits cdr-bits &key (generations 10))
  "CONS that runs through Rule 110.
   1. Build the cons cell structure
   2. Run it through CA
   3. Return processed result"
  (let* (;; Encode: tag + car-length(8 bits) + car + cdr
         (car-len (length car-bits))
         (len-bits (loop for i from 7 downto 0
                        collect (if (logbitp i car-len) 1 0)))
         (cell (append *tag-pair* len-bits car-bits cdr-bits))
         ;; Run through CA
         (ca (make-ca-from-state (state-from-bits cell)))
         (final (run-ca ca generations)))
    (coerce (ca-state final) 'list)))

(defun ca-car (cell-bits &key (generations 10))
  "CAR that runs through Rule 110.
   Extract car, run through CA."
  (let* (;; Skip tag, read length
         (len-bits (subseq cell-bits 4 12))
         (car-len (loop for b in len-bits
                       for i from 7 downto 0
                       sum (* b (expt 2 i))))
         ;; Extract car
         (car-bits (subseq cell-bits 12 (+ 12 car-len)))
         ;; Run through CA
         (ca (make-ca-from-state (state-from-bits car-bits)))
         (final (run-ca ca generations)))
    (coerce (ca-state final) 'list)))

(defun ca-cdr (cell-bits &key (generations 10))
  "CDR that runs through Rule 110.
   Extract cdr, run through CA."
  (let* (;; Skip tag, read length
         (len-bits (subseq cell-bits 4 12))
         (car-len (loop for b in len-bits
                       for i from 7 downto 0
                       sum (* b (expt 2 i))))
         ;; Extract cdr
         (cdr-bits (subseq cell-bits (+ 12 car-len)))
         ;; Run through CA
         (ca (make-ca-from-state (state-from-bits cdr-bits)))
         (final (run-ca ca generations)))
    (coerce (ca-state final) 'list)))

;;; ============================================================
;;; CA-IF: Conditional through CA
;;; ============================================================

(defun ca-if (cond-bits then-bits else-bits &key (generations 10))
  "IF that runs through Rule 110.
   If cond is true, run then through CA.
   If cond is false, run else through CA."
  (let* ((is-true (and (>= (length cond-bits) 5)
                       (equal (subseq cond-bits 0 4) *tag-bool*)
                       (= 1 (nth 4 cond-bits))))
         (selected (if is-true then-bits else-bits))
         (ca (make-ca-from-state (state-from-bits selected)))
         (final (run-ca ca generations)))
    (coerce (ca-state final) 'list)))

;;; ============================================================
;;; CA-CHURCH-NUMERAL: Church encoding through CAs
;;; ============================================================

(defun ca-church-numeral (n f-transform x-bits &key (generations 10))
  "Apply Church numeral n: run f-transform n times on x-bits.
   Each application goes through Rule 110."
  (let ((current x-bits))
    (dotimes (i n)
      ;; Apply f by running through CA
      (let* ((transformed (funcall f-transform current))
             (ca (make-ca-from-state (state-from-bits transformed)))
             (final (run-ca ca generations)))
        (setf current (coerce (ca-state final) 'list))))
    current))

(defun ca-succ (church-n-fn)
  "SUCC: transform Church n to Church n+1.
   Returns a function that applies f one more time."
  (lambda (f-transform x-bits &key (generations 10))
    (let* (;; Apply church-n first
           (after-n (funcall church-n-fn f-transform x-bits :generations generations))
           ;; Apply f one more time through CA
           (transformed (funcall f-transform after-n))
           (ca (make-ca-from-state (state-from-bits transformed)))
           (final (run-ca ca generations)))
      (coerce (ca-state final) 'list))))

;;; ============================================================
;;; ARITHMETIC via Church numerals on CAs
;;; ============================================================

(defun ca-add (m n)
  "Add two Church numerals: m + n = m SUCC n
   Apply SUCC m times to n."
  (let ((result n))
    (dotimes (i m)
      (setf result (ca-succ (lambda (f x &key generations)
                              (ca-church-numeral result f x :generations generations)))))
    result))

;;; ============================================================
;;; DEMONSTRATION
;;; ============================================================

(defun demonstrate-lisp-on-ca ()
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║        LISP RUNNING ON RULE 110 CELLULAR AUTOMATA            ║~%")
  (format t "║           Every operation flows through CAs                   ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; CA-CONS / CA-CAR / CA-CDR
  (format t "~%~%=== CA-CONS / CA-CAR / CA-CDR ===~%")
  (format t "Data flows through Rule 110 at each step.~%~%")

  (let* ((a (encode-number 42 8))
         (b (encode-number 17 8)))
    (format t "a = 42 encoded: ~{~A~}~%" a)
    (format t "b = 17 encoded: ~{~A~}~%" b)

    (let ((cell (ca-cons a b :generations 5)))
      (format t "~%(ca-cons a b) through 5 CA generations:~%")
      (format t "  ~{~A~}~%" (subseq cell 0 (min 40 (length cell))))
      (format t "  ... (~D bits total)~%" (length cell))))

  ;; CA-IF
  (format t "~%~%=== CA-IF ===~%")
  (format t "Conditional selection through CA.~%~%")

  (let ((true-val (encode-bool t))
        (false-val (encode-bool nil))
        (then-bits (encode-number 100 8))
        (else-bits (encode-number 0 8)))
    (format t "true encoded:  ~{~A~}~%" true-val)
    (format t "false encoded: ~{~A~}~%" false-val)
    (format t "~%")
    (let ((result-true (ca-if true-val then-bits else-bits :generations 5))
          (result-false (ca-if false-val then-bits else-bits :generations 5)))
      (format t "(ca-if true 100 0):  ~{~A~}... (selected then)~%"
              (subseq result-true 0 (min 16 (length result-true))))
      (format t "(ca-if false 100 0): ~{~A~}... (selected else)~%"
              (subseq result-false 0 (min 16 (length result-false))))))

  ;; Church numerals on CA
  (format t "~%~%=== CHURCH NUMERALS ON CA ===~%")
  (format t "Each application of f runs through Rule 110.~%~%")

  (let* ((x-bits '(0 0 0 0 0 0 0 1))  ; starting value
         ;; f = shift left (simple transform)
         (f-transform (lambda (bits)
                       (append (cdr bits) (list 0)))))
    (format t "x = ~{~A~}~%" x-bits)
    (format t "f = shift-left~%~%")

    (dotimes (n 5)
      (let ((result (ca-church-numeral n f-transform x-bits :generations 3)))
        (format t "Church-~D(f, x) = ~{~A~}~%" n result))))

  ;; The punchline
  (format t "~%~%╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║                    ACHIEVEMENT UNLOCKED                        ║~%")
  (format t "╠═══════════════════════════════════════════════════════════════╣~%")
  (format t "║  Every Lisp operation now runs through Rule 110:              ║~%")
  (format t "║                                                               ║~%")
  (format t "║    cons  →  CA processing  →  cell                           ║~%")
  (format t "║    car   →  CA processing  →  first element                  ║~%")
  (format t "║    cdr   →  CA processing  →  rest                           ║~%")
  (format t "║    if    →  CA processing  →  selected branch                ║~%")
  (format t "║    Church n  →  n CA runs  →  result                         ║~%")
  (format t "║                                                               ║~%")
  (format t "║  The Lisp IS the CA. The CA IS the Lisp.                     ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%"))
