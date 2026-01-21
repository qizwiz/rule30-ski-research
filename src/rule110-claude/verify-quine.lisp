;;;; Verify the discovered quine

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")

(defpackage :verify-quine (:use :cl :rule110))
(in-package :verify-quine)

(defparameter *quine-32* '(1 1 0 0 0 1 1 1 1 1 0 0 0 1 1 1 1 1 0 0 0 1 1 1 1 1 0 0 0 1 1 1))

(format t "~%=== VERIFYING 32-BIT QUINE ===~%~%")
(format t "Initial state: ~{~A~}~%" *quine-32*)

(let* ((ca (make-ca-from-state (state-from-bits *quine-32*)))
       (final (run-ca ca 16))
       (output (coerce (ca-state final) 'list)))
  (format t "After 16 gens: ~{~A~}~%" output)
  (format t "~%Match: ~A~%" (if (equal *quine-32* output) "*** VERIFIED QUINE! ***" "NOT A QUINE"))

  ;; Show the evolution
  (format t "~%Evolution:~%")
  (let ((ca (make-ca-from-state (state-from-bits *quine-32*))))
    (dotimes (i 17)
      (format t "Gen ~2D: ~{~A~}~%" i (coerce (ca-state ca) 'list))
      (setf ca (step-ca ca)))))

(sb-ext:quit)
