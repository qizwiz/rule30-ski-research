;;;; rule110.lisp - Rule 110 Cellular Automaton
;;;; The computational substrate for emergent Lisp
;;;;
;;;; Rule 110: One of the simplest Turing-complete systems known
;;;; Truth table:
;;;;   111 -> 0
;;;;   110 -> 1
;;;;   101 -> 1
;;;;   100 -> 0
;;;;   011 -> 1
;;;;   010 -> 1
;;;;   001 -> 1
;;;;   000 -> 0
;;;;
;;;; Binary: 01101110 = 110

(defpackage :rule110
  (:use :cl)
  (:export #:make-ca
           #:make-ca-from-state
           #:step-ca
           #:run-ca
           #:ca
           #:ca-state
           #:ca-width
           #:ca-generation
           #:ca-to-bits
           #:bits-to-string
           #:bits-to-ascii
           #:ca-to-string
           #:random-initial-state
           #:state-from-bits
           #:print-ca
           #:demo))

(in-package :rule110)

;;; Rule 110 transition function
(defun rule110-cell (left center right)
  "Apply Rule 110 to a neighborhood of 3 cells.
   Returns the new center cell value."
  (let ((pattern (+ (* 4 left) (* 2 center) right)))
    ;; Rule 110 = 01101110 in binary
    ;; pattern 7 (111) -> 0
    ;; pattern 6 (110) -> 1
    ;; pattern 5 (101) -> 1
    ;; pattern 4 (100) -> 0
    ;; pattern 3 (011) -> 1
    ;; pattern 2 (010) -> 1
    ;; pattern 1 (001) -> 1
    ;; pattern 0 (000) -> 0
    (if (logbitp pattern 110) 1 0)))

;;; CA Structure
(defstruct ca
  (state #() :type simple-vector)  ; current row of cells
  (width 0 :type fixnum)           ; number of cells
  (generation 0 :type fixnum))     ; current generation

(defun make-ca-from-state (initial-state)
  "Create a CA from an initial state vector."
  (make-ca :state (coerce initial-state 'simple-vector)
           :width (length initial-state)
           :generation 0))

(defun random-initial-state (width &optional (density 0.5))
  "Generate a random initial state with given density of 1s."
  (let ((state (make-array width :initial-element 0)))
    (dotimes (i width)
      (when (< (random 1.0) density)
        (setf (aref state i) 1)))
    state))

(defun state-from-bits (bits)
  "Create state from a list of bits."
  (coerce bits 'simple-vector))

;;; Evolution
(defun step-ca (ca)
  "Evolve the CA one generation. Returns a new CA."
  (let* ((state (ca-state ca))
         (width (ca-width ca))
         (new-state (make-array width :initial-element 0)))
    ;; Apply rule to each cell (with wraparound boundary)
    (dotimes (i width)
      (let ((left (aref state (mod (1- i) width)))
            (center (aref state i))
            (right (aref state (mod (1+ i) width))))
        (setf (aref new-state i) (rule110-cell left center right))))
    (make-ca :state new-state
             :width width
             :generation (1+ (ca-generation ca)))))

(defun run-ca (ca generations)
  "Run the CA for N generations. Returns final CA."
  (loop repeat generations
        do (setf ca (step-ca ca)))
  ca)

;;; Output interpretation
(defun ca-to-bits (ca)
  "Extract the current state as a list of bits."
  (coerce (ca-state ca) 'list))

(defun bits-to-ascii (bits)
  "Interpret bits as ASCII characters (8 bits per char)."
  (let ((chars '()))
    (loop for i from 0 below (length bits) by 8
          for byte = (loop for j from 0 below 8
                          for bit-idx = (+ i j)
                          when (< bit-idx (length bits))
                          sum (* (nth bit-idx bits) (expt 2 (- 7 j))))
          when (and (> byte 0) (<= byte 127))
          do (push (code-char byte) chars))
    (coerce (nreverse chars) 'string)))

(defun ca-to-string (ca)
  "Convert CA state to ASCII string interpretation."
  (bits-to-ascii (ca-to-bits ca)))

(defun print-ca (ca &optional (stream t))
  "Print CA state visually."
  (format stream "Gen ~4D: " (ca-generation ca))
  (loop for cell across (ca-state ca)
        do (format stream "~A" (if (= cell 1) "#" " ")))
  (terpri stream))

;;; For REPL testing
(defun demo ()
  "Quick demo of Rule 110."
  (let ((ca (make-ca-from-state (state-from-bits '(0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0)))))
    (dotimes (i 10)
      (print-ca ca)
      (setf ca (step-ca ca)))
    ca))
