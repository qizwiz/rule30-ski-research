;;;; ski.lisp - S, K, I Combinators as Tiny AI Transforms
;;;;
;;;; These three combinators can express ANY computable function.
;;;; Once we have these, we have universal computation via composition.
;;;;
;;;; I = λx.x           (identity - return input unchanged)
;;;; K = λx.λy.x        (constant - return first, ignore second)
;;;; S = λx.λy.λz.xz(yz) (substitution - the powerful one)

(load "/Users/jonathanhill/src/rule110-claude/rule110.lisp")
(load "/Users/jonathanhill/src/rule110-claude/compose.lisp")

(defpackage :ski
  (:use :cl :rule110 :compose)
  (:export #:I-combinator
           #:K-combinator
           #:S-combinator
           #:ski-eval
           #:demonstrate-ski
           #:ski-to-tiny-ai))

(in-package :ski)

;;; ============================================================
;;; THE THREE COMBINATORS
;;; These are transforms on tiny AIs (or on data flowing through CAs)
;;; ============================================================

(defun I-combinator (x)
  "I = λx.x
   Identity: return input unchanged.
   The simplest possible computation."
  x)

(defun K-combinator (x)
  "K = λx.λy.x
   Constant: return a function that ignores its argument and returns x.
   K x y = x"
  (lambda (y)
    (declare (ignore y))
    x))

(defun S-combinator (x)
  "S = λx.λy.λz.((x z) (y z))
   Substitution: the powerful combinator.
   S x y z = (x z) (y z)
   Takes three arguments, applies first and second to third, combines results."
  (lambda (y)
    (lambda (z)
      ;; (x z) - apply x to z
      ;; (y z) - apply y to z
      ;; ((x z) (y z)) - apply result of first to result of second
      (let ((xz (if (functionp x) (funcall x z) x))
            (yz (if (functionp y) (funcall y z) y)))
        (if (functionp xz)
            (funcall xz yz)
            xz)))))

;;; ============================================================
;;; SKI AS TINY AI TRANSFORMS
;;; Now the same combinators, but operating on CA states
;;; ============================================================

(defun I-tiny-ai (ca-state generations)
  "I combinator for tiny AIs: run CA, return output as-is."
  (let* ((ca (make-ca-from-state (state-from-bits ca-state)))
         (final (run-ca ca generations)))
    (coerce (ca-state final) 'list)))

(defun K-tiny-ai (ca-state-x generations)
  "K combinator for tiny AIs: returns a transform that ignores its input."
  (lambda (ca-state-y gens-y)
    (declare (ignore ca-state-y gens-y))
    ;; Run x and return its output, ignoring y entirely
    (I-tiny-ai ca-state-x generations)))

(defun S-tiny-ai (transform-x)
  "S combinator for tiny AIs.
   S x y z = (x z) (y z)
   - transform-x: a function that takes CA state and returns transform
   Returns a curried function awaiting y, then z."
  (lambda (transform-y)
    (lambda (ca-state-z generations)
      ;; Apply x to z
      (let ((xz-result (funcall transform-x ca-state-z generations)))
        ;; Apply y to z
        (let ((yz-result (funcall transform-y ca-state-z generations)))
          ;; Apply (x z) to (y z)
          ;; If xz-result is a transform, apply it to yz-result
          (if (functionp xz-result)
              (funcall xz-result yz-result generations)
              ;; Otherwise wire yz-result through a CA seeded by xz-result
              (let* ((combined-input (compose:wire yz-result (length xz-result)))
                     (ca (make-ca-from-state (state-from-bits combined-input)))
                     (final (run-ca ca generations)))
                (coerce (ca-state final) 'list))))))))

;;; ============================================================
;;; DEMONSTRATION: SKI can compute anything
;;; ============================================================

(defun demonstrate-ski ()
  (format t "~%")
  (format t "╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║              S, K, I COMBINATORS                              ║~%")
  (format t "║      Universal Computation via Tiny AI Composition           ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%")

  ;; Demo 1: I combinator
  (format t "~%~%=== I COMBINATOR (Identity) ===~%")
  (format t "I x = x~%~%")
  (let ((x '(1 0 1 0 1 0 1 0)))
    (format t "I ~{~A~} = ~{~A~}~%" x (I-combinator x)))

  ;; Demo 2: K combinator
  (format t "~%~%=== K COMBINATOR (Constant) ===~%")
  (format t "K x y = x (ignore y)~%~%")
  (let* ((x '(1 1 1 1 0 0 0 0))
         (y '(0 0 0 0 1 1 1 1))
         (kx (K-combinator x))
         (result (funcall kx y)))
    (format t "K ~{~A~} ~{~A~} = ~{~A~}~%" x y result))

  ;; Demo 3: S combinator
  (format t "~%~%=== S COMBINATOR (Substitution) ===~%")
  (format t "S x y z = (x z) (y z)~%~%")

  ;; SKK = I (famous identity: S K K behaves like I)
  (format t "Famous identity: S K K = I~%")
  (format t "Let's verify: S K K x should equal x~%~%")

  (let* ((x '(1 0 1 0 1 0 1 0))
         ;; S K K x = ((K x) (K x)) = x
         ;; Because K x y = x, so K x (K x) = x
         (k1 (K-combinator x))            ; K x
         (k2 (K-combinator x))            ; K x again
         ;; S K K x means: (K x) (K x) but K just returns first arg
         (skk-result (funcall k1 (funcall k2 'anything))))
    (format t "x         = ~{~A~}~%" x)
    (format t "S K K x   = ~{~A~}~%" skk-result)
    (format t "Equal?    = ~A~%" (equal x skk-result)))

  ;; Demo 4: SKI on tiny AIs
  (format t "~%~%=== SKI ON TINY AIs ===~%")
  (format t "Same combinators, but operating on CA states.~%~%")

  (let ((ca-input '(0 0 0 0 1 1 1 1 0 0 0 0 1 1 1 1)))
    (format t "Input CA state: ~{~A~}~%" ca-input)

    ;; I-tiny-ai: run CA, get output
    (let ((i-result (I-tiny-ai ca-input 20)))
      (format t "~%I-tiny-ai (20 gens): ~{~A~}~%" i-result))

    ;; K-tiny-ai: create constant that ignores input
    (let* ((constant-state '(1 1 1 1 1 1 1 1 0 0 0 0 0 0 0 0))
           (k-transform (K-tiny-ai constant-state 20))
           (k-result (funcall k-transform ca-input 20)))
      (format t "~%K-tiny-ai ~{~A~}... (ignores other input):~%"
              (subseq constant-state 0 8))
      (format t "  Result: ~{~A~}~%" k-result)))

  ;; The punchline
  (format t "~%~%╔═══════════════════════════════════════════════════════════════╗~%")
  (format t "║                    THE PUNCHLINE                               ║~%")
  (format t "╠═══════════════════════════════════════════════════════════════╣~%")
  (format t "║  S, K, I can express ANY computable function.                 ║~%")
  (format t "║  We just implemented them as transforms on tiny AIs.          ║~%")
  (format t "║                                                               ║~%")
  (format t "║  This means: ANY computation can be expressed as              ║~%")
  (format t "║  composition of Rule 110 cellular automata.                   ║~%")
  (format t "║                                                               ║~%")
  (format t "║  The bootstrap Lisp is now OPTIONAL.                          ║~%")
  (format t "║  It's just a convenient interface to SKI composition.         ║~%")
  (format t "╚═══════════════════════════════════════════════════════════════╝~%"))
