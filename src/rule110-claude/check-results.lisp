;;;; check-results.lisp - Quick check of what's been discovered
;;;; Usage: sbcl --script check-results.lisp

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")

(defpackage :check-results
  (:use :cl :rule110))

(in-package :check-results)

(defun list-result-files ()
  "List all result files."
  (directory "/Users/jonathanhill/src/rule110-claude/results/*.lisp"))

(defun load-result (filepath)
  "Load and display a result file."
  (with-open-file (in filepath)
    (read in)))

(defun verify-result (result)
  "Verify a loaded result."
  (let* ((name (first result))
         (plist (rest result))
         (initial (getf plist :initial-state))
         (target (getf plist :target-bits))
         (gens (getf plist :ca-generations))
         (pos (getf plist :verified-position)))
    (when (and initial target gens (>= pos 0))
      (let* ((ca (make-ca-from-state (state-from-bits initial)))
             (final (run-ca ca gens))
             (output (coerce (ca-state final) 'list))
             (window (when (>= (length output) (+ pos (length target)))
                      (subseq output pos (+ pos (length target))))))
        (values (equal window target) window target pos)))))

(defun main ()
  (format t "~%=== CHECKING DISCOVERY RESULTS ===~%~%")
  (let ((files (list-result-files)))
    (if (null files)
        (format t "No results yet. Run: sbcl --script local-runner.lisp~%")
        (dolist (f files)
          (format t "~%--- ~A ---~%" (file-namestring f))
          (let ((result (load-result f)))
            (format t "Name: ~A~%" (first result))
            (let ((plist (rest result)))
              (format t "Target: ~{~A~}~%" (getf plist :target-bits))
              (format t "CA gens: ~D~%" (getf plist :ca-generations))
              (format t "Position: ~D~%" (getf plist :verified-position)))
            (multiple-value-bind (ok window target pos) (verify-result result)
              (if ok
                  (format t "STATUS: *** VERIFIED ***~%")
                  (format t "STATUS: unverified or partial~%"))))))))

(main)
(quit)
