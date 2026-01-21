;;;; registry.lisp - The registry of discovered Tiny AIs
;;;; This is the first concrete result of Rule 110 Lisp Genesis

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")

(defpackage :genesis-registry
  (:use :cl :rule110)
  (:export #:*tiny-ais*
           #:get-tiny-ai
           #:run-tiny-ai
           #:verify-tiny-ai
           #:list-tiny-ais
           #:*emergent-encoding*
           #:demo))

(in-package :genesis-registry)

;;; The Emergent Encoding
;;; These patterns were DISCOVERED by observing Rule 110's natural dynamics
(defparameter *emergent-encoding*
  '((:lparen . (1 1 0 0 1 1 0 0 0 1 0 0 1 1 0 1))
    (:rparen . (0 0 0 1 1 1 1 1 0 0 0 1 0 0 1 1))
    (:nil    . (1 1 0 0 1 1 0 0 0 1 0 0 1 1 0 1 0 0 0 1 1 1 1 1 0 0 0 1 0 0 1 1))))

;;; The Registry of Discovered Tiny AIs
;;; Each entry: (name initial-state ca-generations verified-position)
(defparameter *tiny-ais*
  '((:lparen
     (1 1 1 0 1 1 1 0 0 0 0 1 1 0 0 0 1 0 0 1 0 1 1 0 0 1 0 1 0 1 1 0)
     40
     11
     "Produces emergent '(' pattern")

    (:rparen
     (0 1 0 0 0 1 1 1 0 1 1 0 1 0 1 0 0 1 0 1 0 0 0 1 0 0 1 0 0 0 0 1)
     40
     4
     "Produces emergent ')' pattern")

    (:nil
     (0 1 0 0 1 1 0 0 1 1 0 1 1 1 0 1 1 1 0 1 0 0 1 0 0 0 1 0 0 1 0 1
      0 0 1 0 0 1 1 0 1 1 1 1 0 1 0 1 0 0 1 1 0 0 1 1 0 0 1 0 1 0 1 1)
     50
     24
     "Produces emergent '()' = NIL pattern")))

(defun get-tiny-ai (name)
  "Retrieve a tiny AI by name."
  (assoc name *tiny-ais*))

(defun run-tiny-ai (name)
  "Execute a tiny AI and return its output bits."
  (let ((entry (get-tiny-ai name)))
    (when entry
      (destructuring-bind (n initial gens pos desc) entry
        (declare (ignore n pos desc))
        (let* ((ca (make-ca-from-state (state-from-bits initial)))
               (final (run-ca ca gens)))
          (ca-to-bits final))))))

(defun verify-tiny-ai (name)
  "Verify a tiny AI produces its expected pattern."
  (let ((entry (get-tiny-ai name))
        (expected (cdr (assoc name *emergent-encoding*))))
    (when (and entry expected)
      (destructuring-bind (n initial gens pos desc) entry
        (declare (ignore n desc))
        (let* ((output (run-tiny-ai name))
               (pattern-at-pos (when (>= (length output) (+ pos (length expected)))
                                (subseq output pos (+ pos (length expected))))))
          (values (equal pattern-at-pos expected)
                  pattern-at-pos
                  expected
                  pos))))))

(defun list-tiny-ais ()
  "List all registered tiny AIs."
  (format t "~%=== GENESIS REGISTRY ===~%")
  (format t "Discovered Tiny AIs:~%~%")
  (dolist (entry *tiny-ais*)
    (destructuring-bind (name initial gens pos desc) entry
      (format t "  ~10A - ~A~%" name desc)
      (format t "             Initial: ~{~A~} (~D bits)~%"
              (subseq initial 0 (min 20 (length initial)))
              (length initial))
      (format t "             Generations: ~D, Position: ~D~%~%" gens pos)))
  (format t "========================~%"))

;;; Demo function
(defun demo ()
  "Demonstrate the tiny AI registry."
  (format t "~%╔════════════════════════════════════════════════════════════════╗~%")
  (format t "║           RULE 110 LISP GENESIS - TINY AI DEMO                  ║~%")
  (format t "╚════════════════════════════════════════════════════════════════╝~%")

  (list-tiny-ais)

  (format t "~%=== VERIFICATION ===~%~%")
  (dolist (name '(:lparen :rparen :nil))
    (multiple-value-bind (ok actual expected pos) (verify-tiny-ai name)
      (format t "~10A: ~A~%" name (if ok "VERIFIED" "FAILED"))
      (when ok
        (format t "           Expected at pos ~D: ~{~A~}~%" pos expected)
        (format t "           Got:                ~{~A~}~%~%" actual))))

  (format t "~%=== RUNNING NIL TINY AI ===~%")
  (let ((output (run-tiny-ai :nil)))
    (format t "Full output (~D bits):~%" (length output))
    (format t "~{~A~}~%" output)))
