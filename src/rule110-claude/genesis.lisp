;;;; genesis.lisp - The main entry point for Rule 110 Lisp Genesis
;;;; This is the "impure" Common Lisp that will eventually replace itself

(defpackage :genesis
  (:use :cl)
  (:export #:run
           #:quick-test
           #:status
           #:explain
           #:demo-rule110))

(in-package :genesis)

;;; Load order matters
(defun load-system ()
  "Load all components."
  (let ((base-path (make-pathname :directory (pathname-directory *load-pathname*))))
    (load (merge-pathnames "rule110.lisp" base-path))
    (load (merge-pathnames "search.lisp" base-path))
    (load (merge-pathnames "tiny-ai.lisp" base-path))))

;;; Main entry points

(defun quick-test ()
  "Quick test - just try to find ()"
  (format t "~%Quick test: searching for '()'...~%")
  (let ((result (ca-search:find-ca-for-target "()"
                                               :ca-width 32
                                               :ca-generations 15
                                               :population-size 50
                                               :max-generations 300)))
    (if (= (ca-search:search-result-fitness result) 16)  ; "()" = 16 bits
        (progn
          (format t "~%SUCCESS! Found CA that produces ()~%")
          (format t "Initial state: ~A~%" (ca-search:search-result-initial-state result))
          t)
        (progn
          (format t "~%Not found in time. Best: ~D/16 bits~%"
                  (ca-search:search-result-fitness result))
          nil))))

(defun run ()
  "Run the full bootstrap sequence."
  (tiny-ai:bootstrap-all))

(defun status ()
  "Show current status of discovered tiny AIs."
  (tiny-ai:show-registry))

;;; REPL helpers
(defun demo-rule110 ()
  "Show Rule 110 in action."
  (format t "~%Rule 110 Demo:~%")
  (let ((ca (rule110:make-ca-from-state
             (rule110:state-from-bits '(0 0 0 0 0 0 0 0 0 0 1 0 0 0 0 0 0 0 0 0)))))
    (dotimes (i 15)
      (format t "~2D: " i)
      (loop for cell across (rule110:ca-state ca)
            do (format t "~A" (if (= cell 1) "█" " ")))
      (format t "~%")
      (setf ca (rule110:step-ca ca)))))

;;; The philosophical core
(defun explain ()
  "Explain what we're doing."
  (format t "
╔══════════════════════════════════════════════════════════════════════╗
║                    RULE 110 LISP GENESIS                              ║
║                                                                       ║
║  We are building Lisp from the ground up using Rule 110 cellular     ║
║  automata as the computational substrate.                             ║
║                                                                       ║
║  The process:                                                         ║
║  1. Start with 'impure' Common Lisp (this code)                      ║
║  2. Use genetic search to find CA initial conditions                  ║
║     that produce Church encodings (pure parentheses)                  ║
║  3. Each successful search creates a 'tiny AI'                        ║
║  4. Compose tiny AIs to build larger structures                       ║
║  5. Eventually replace this bootstrap code with tiny AIs              ║
║                                                                       ║
║  Church encodings are our fitness targets:                            ║
║  - NIL:      ()                                                       ║
║  - Identity: (lambda (x) x)                                           ║
║  - Church 0: (lambda (f) (lambda (x) x))                             ║
║  - Church 1: (lambda (f) (lambda (x) (f x)))                         ║
║  - SUCC:     (lambda (n) (lambda (f) (lambda (x) (f ((n f) x)))))    ║
║                                                                       ║
║  The goal: a self-replacing quine where the compiler IS the AI.       ║
╚══════════════════════════════════════════════════════════════════════╝
"))
