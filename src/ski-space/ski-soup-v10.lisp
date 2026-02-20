;;;; ski-soup-v8.lisp
;;;;
;;;; SKI soup v7 + ADAPTIVE TOPOLOGY (Deacon reciprocal coupling).
;;;;
;;;; KEY UPGRADE FROM V7:
;;;;
;;;; ADAPTIVE TOPOLOGY — THE CONTAINER GROWS FROM THE CHEMISTRY
;;;;   In v7, topology (small-world graph) is fixed at init and never changes.
;;;;   In v8, the adjacency graph REWIRES ITSELF based on RAF contribution:
;;;;
;;;;   After each report window:
;;;;   - Compute each tape's RAF score: how often does its hash appear as a
;;;;     PRODUCT in the reaction graph? (i.e., how catalytically productive is it?)
;;;;   - High-RAF tapes gain a neighbor edge (attract new interaction partners)
;;;;   - Low-RAF tapes (below mean) shed one edge (become isolated)
;;;;   - Minimum degree 1 enforced (no tape fully disconnected)
;;;;   - Maximum degree capped at n-tapes/4 (no tape dominates everything)
;;;;
;;;;   This closes Deacon's loop: autocatalysis shapes the container,
;;;;   container shapes autocatalysis. The topology is now a PRODUCT of
;;;;   the chemistry, not a fixed parameter.
;;;;
;;;;   New output: topo-edges (total edge count), topo-mean-degree,
;;;;               topo-max-degree — watch the graph breathe.

(defpackage :ski-soup-v10
  (:use :cl)
  (:export #:run-soup #:main #:run-grid #:run-small-world #:run-spatial #:make-small-world
           #:reset-rxn-graph! #:run-multiregion))

(in-package :ski-soup-v10)

;;; ============================================================
;;; TAPE: fixed-length symbol vector (identical to v3)
;;; ============================================================

(defparameter *L* 16
  "Tape length. BFF uses 64; we use 16 for faster computation.")

(defparameter *alphabet* #(:S :S :S :K :K :I)
  "Symbol weights: 3S:2K:1I — biased toward duplication.")

(defun rand-sym () (aref *alphabet* (random (length *alphabet*))))

(defstruct (tape (:conc-name t-)
                 (:copier nil))
  (syms (make-array *L* :initial-element :I) :type simple-vector)
  (ops 0 :type fixnum)
  (gen 0 :type fixnum))

(defun fresh-tape ()
  (let ((v (make-array *L*)))
    (dotimes (i *L*) (setf (aref v i) (rand-sym)))
    (make-tape :syms v)))

;;; ============================================================
;;; TREE NODE (identical to v3)
;;; ============================================================

(defstruct (node (:conc-name n-)
                 (:copier nil))
  (type :atom :type keyword)
  (sym nil)
  (left nil)
  (right nil))

;;; ============================================================
;;; PARSE (identical to v3)
;;; ============================================================

(defun parse-syms (syms start end)
  (let ((n (- end start)))
    (case n
      (0 (make-node :type :atom :sym :I))
      (1 (make-node :type :atom :sym (aref syms start)))
      (t (let ((acc (make-node :type :atom :sym (aref syms start))))
           (loop for i from (1+ start) below end do
             (setf acc (make-node :type :app
                                  :left acc
                                  :right (make-node :type :atom :sym (aref syms i)))))
           acc)))))

;;; ============================================================
;;; SERIALIZE (identical to v3, nil-guarded)
;;; ============================================================

(defun serialize (node &optional (depth 0))
  (when (or (null node) (> depth (* 4 *L*))) (return-from serialize (list :I)))
  (if (eq (n-type node) :app)
      (append (serialize (n-left node) (1+ depth))
              (serialize (n-right node) (1+ depth)))
      (list (n-sym node))))

;;; ============================================================
;;; REDUCTION (identical to v3, fixed S-rule)
;;; ============================================================

(defun copy-node (n &optional (depth 0))
  (when (or (null n) (> depth (* 4 *L*))) (return-from copy-node (make-node :type :atom :sym :I)))
  (if (eq (n-type n) :app)
      (make-node :type :app
                 :left (copy-node (n-left n) (1+ depth))
                 :right (copy-node (n-right n) (1+ depth)))
      (make-node :type :atom :sym (n-sym n))))

(defun node-size (n &optional (depth 0))
  (if (or (null n) (> depth (* 4 *L*))) 0
      (if (eq (n-type n) :app)
          (+ 1 (node-size (n-left n) (1+ depth))
               (node-size (n-right n) (1+ depth)))
          1)))

(defparameter *pressure-scale* 64.0
  "Multiplier: surface-pressure * scale = reduction steps this interaction.
   At scale=64, a root-level redex fires 64 times. A depth-6 redex fires 1 time.
   This is the 'tempo' of the material — higher = faster decay everywhere.")

(defparameter *max-nodes* (* 8 *L*))

;;; ============================================================
;;; METRICS — data-driven per-epoch report
;;; Each entry: (label thunk format-spec)
;;;   label      = string shown as "label=value" in the epoch line
;;;   thunk      = lambda (ctx) -> value, where ctx is a plist with
;;;                :epoch :tv :n-tapes :ops-per-int :rate :H :unique :min-rep
;;;   format-spec = format directive string e.g. "~,3F" or "~D"
;;; The epoch line is built dynamically from this list.
;;; To add SCC: push '("scc%" (lambda (ctx) (* 100.0 (nth-value 2 (scc-rxn-graph)))) "~,1F") *metrics*
;;; To remove cycles: (setf *metrics* (remove "cyc" *metrics* :key #'car :test #'equal))
;;; ============================================================

(defparameter *metrics*
  (list
   (list "ops/int" (lambda (ctx) (getf ctx :ops-per-int))                                "~,3F")
   (list "reps"    (lambda (ctx) (count-replicators (getf ctx :tv)
                                                    (getf ctx :min-rep))) "~D")
   (list "cat"     (lambda (ctx) (declare (ignore ctx))
                                 (catalysis-probability))                                 "~,4F")
   (list "RAF"     (lambda (ctx) (raf-threshold (getf ctx :n-tapes)))                    "~,3F")
   (list "cyc"     (lambda (ctx) (declare (ignore ctx))
                                 (count-cycles-fast))                                     "~D"))
  "Per-epoch metrics list. Each entry: (label thunk format-spec).
   thunk receives a plist: :epoch :tv :n-tapes :ops-per-int :rate :H :unique :min-rep
   Metrics are rendered as 'label=value' separated by ' | '.
   Add/remove entries to change what appears in each epoch line.")

(defun render-epoch-line (ctx)
  "Build the epoch report line from *metrics*."
  (let* ((epoch   (getf ctx :epoch))
         (H       (getf ctx :H))
         (unique  (getf ctx :unique))
         (n-tapes (getf ctx :n-tapes))
         (rate    (getf ctx :rate))
         (parts   (loop for (label thunk fmt) in *metrics*
                        collect (format nil (concatenate 'string "~A=" fmt)
                                        label (funcall thunk ctx)))))
    (format nil "E~8D | H=~,3F u=~D/~D | ~{~A~^ | ~} | ~,0F/s"
            epoch H unique n-tapes parts rate)))

(defun prune! (n &optional (max-d 7))
  (labels ((p (c d)
             (when (and c (eq (n-type c) :app))
               (if (>= d max-d)
                   (setf (n-type c) :atom (n-sym c) (rand-sym)
                         (n-left c) nil (n-right c) nil)
                   (progn (p (n-left c) (1+ d))
                          (p (n-right c) (1+ d)))))))
    (p n 0)))

(defun reduce-step! (c &optional (depth 0))
  (when (or (null c) (> depth (* 4 *L*))) (return-from reduce-step! nil))
  (unless (eq (n-type c) :app) (return-from reduce-step! nil))
  (let ((fn (n-left c))
        (arg (n-right c)))
    (unless fn (return-from reduce-step! nil))
    (cond
      ;; I x → x
      ((and (eq (n-type fn) :atom) (eq (n-sym fn) :I))
       (when arg
         (setf (n-type c) (n-type arg) (n-sym c) (n-sym arg)
               (n-left c) (n-left arg) (n-right c) (n-right arg))
         t))
      ;; K x y → x
      ((and (eq (n-type fn) :app)
            (n-left fn)
            (eq (n-type (n-left fn)) :atom)
            (eq (n-sym (n-left fn)) :K))
       (let ((x (n-right fn)))
         (when x
           (setf (n-type c) (n-type x) (n-sym c) (n-sym x)
                 (n-left c) (n-left x) (n-right c) (n-right x))
           t)))
      ;; S x y z → (x z)(y z)
      ((and (eq (n-type fn) :app)
            (n-left fn)
            (eq (n-type (n-left fn)) :app)
            (n-left (n-left fn))
            (eq (n-type (n-left (n-left fn))) :atom)
            (eq (n-sym (n-left (n-left fn))) :S))
       (let* ((sx  (n-left fn))
              (x   (n-right sx))
              (y   (n-right fn))
              (z   arg)
              (z2  (copy-node z)))
         (when (and x y z z2)
           (setf (n-type c) :app
                 (n-left c) (make-node :type :app :left x :right z)
                 (n-right c) (make-node :type :app :left y :right z2))
           t)))
      ;; W x y → x y y  (duplication without third arg — more direct than S)
      ((and (eq (n-type fn) :app)
            (n-left fn)
            (eq (n-type (n-left fn)) :atom)
            (eq (n-sym (n-left fn)) :W))
       (let* ((x   (n-right fn))
              (y   arg)
              (y2  (copy-node y)))
         (when (and x y y2)
           (setf (n-type c) :app
                 (n-left c) (make-node :type :app :left x :right y)
                 (n-right c) y2)
           t)))
      ;; B x y z → x (y z)  (composition)
      ((and (eq (n-type fn) :app)
            (n-left fn)
            (eq (n-type (n-left fn)) :app)
            (n-left (n-left fn))
            (eq (n-type (n-left (n-left fn))) :atom)
            (eq (n-sym (n-left (n-left fn))) :B))
       (let* ((bx  (n-left fn))
              (x   (n-right bx))
              (y   (n-right fn))
              (z   arg))
         (when (and x y z)
           (setf (n-type c) :app
                 (n-left c) x
                 (n-right c) (make-node :type :app :left y :right z))
           t)))
      (t (or (reduce-step! fn (1+ depth))
             (reduce-step! arg (1+ depth)))))))

(defvar *total-ops* 0)
(defvar *total-interactions* 0)
(defvar *window-ops* 0)

;;; ============================================================
;;; DA VINCI SURFACE PRESSURE
;;;
;;; Walk the tree, propagating pressure p/2 to each child at APP nodes.
;;; At leaves: check if this position is a reducible redex head.
;;; A node is a redex head if it's the function position of an APP
;;; that has enough arguments to fire (I needs 1, K needs 2, S needs 3).
;;; We approximate: count atoms that ARE combinators at leaves —
;;; their pressure contribution is their inherited pressure.
;;; ============================================================

;;; Murray's cube rule branching factor: at each APP node, each child
;;; receives pressure * MURRAY-FACTOR where MURRAY-FACTOR = 2^(-2/3).
;;; This conserves r^3 (not r^2) at each split — the animal vascular law.
;;; Result: deeper structure decays more slowly than da Vinci, more memory.
(defparameter *murray-exponent* (/ -2.0 3.0)
  "Exponent in Murray's branching rule: factor = 2^exponent per branch level.
   -2/3 is the biological cube rule. Genome-evolvable: range [-1.0, 0.0].
   0.0 = no decay (flat pressure), -1.0 = very steep decay (shallow trees only).")

(defun surface-pressure (node &optional (p 1.0) (depth 0))
  "Murray branching rule: pressure scales as 2^*murray-exponent* per branch level.
   Exponent is genome-evolvable — controls depth sensitivity of the pressure field."
  (when (or (null node) (> depth (* 4 *L*))) (return-from surface-pressure 0.0))
  (let ((factor (expt 2.0 *murray-exponent*)))
    (if (eq (n-type node) :app)
        ;; Branch: each child gets p * factor
        (+ (surface-pressure (n-left node)  (* p factor) (1+ depth))
           (surface-pressure (n-right node) (* p factor) (1+ depth)))
        ;; Leaf: contribute pressure if it's a combinator (potential redex head)
        (if (member (n-sym node) '(:S :K :I))
            p
            0.0))))

(defun reduce-by-pressure! (tree)
  "Fire reductions proportional to Murray surface pressure.
   High pressure = shallow active redexes = fast metabolism.
   Low pressure = deep or K-sealed structure = slow metabolism, long memory.
   Returns steps fired."
  (let* ((pressure (surface-pressure tree))
         (steps    (max 1 (round (* pressure *pressure-scale*)))))
    (loop for i from 0 below steps
          while (reduce-step! tree)
          do (when (> (node-size tree) *max-nodes*)
               (prune! tree)
               (return (1+ i)))
          finally (return i))))

;;; ============================================================
;;; CATALYSIS MEASUREMENT
;;; Estimate per-pair catalysis probability p empirically.
;;; A tape A "catalyzes" tape B's reaction with C if the output
;;; of (A,B) has higher surface pressure than B alone.
;;; We sample this periodically to track RAF threshold proximity.
;;; ============================================================

(defvar *catalysis-events* 0
  "Count of interactions where output pressure > max(input pressures).")
(defvar *catalysis-samples* 0
  "Total interactions sampled for catalysis measurement.")

(defun measure-catalysis! (ops out-len)
  "Catalytic if interaction produced more than 1 reduction per symbol —
   output is structurally richer than either input alone."
  (incf *catalysis-samples*)
  (when (> ops out-len)
    (incf *catalysis-events*)))

(defun catalysis-probability ()
  "Empirical per-pair catalysis probability."
  (if (zerop *catalysis-samples*) 0.0
      (/ (float *catalysis-events*) *catalysis-samples*)))

(defun raf-threshold (n-tapes)
  "Jain-Krishna RAF threshold: need N > 0.693/p for autocatalytic closure.
   Returns ratio actual-N / threshold-N. >1.0 means RAF likely."
  (let ((p (catalysis-probability)))
    (if (zerop p) 0.0
        (/ (* n-tapes p) 0.693))))

;;; ============================================================
;;; REACTION GRAPH — cycle detection for RAF measurement
;;;
;;; We maintain a sliding window of recent reactions:
;;;   (hash-a, hash-b) → (hash-out-a, hash-out-b)
;;; Then search for cycles: does hash-out-a eventually lead back to hash-a?
;;; A 2-cycle: A+B→C+D, C+D→A+B  (mutual catalysis)
;;; A 3-cycle: A+B→C, C+D→E, E+F→A  (collective autocatalysis)
;;; ============================================================

(defparameter *rxn-window-size* 2000
  "Number of recent reactions to keep in the reaction graph. Genome-evolvable.")

(defvar *rxn-graph* (make-hash-table :test 'equal)
  "Maps (hash-a . hash-b) → hash-output-a.
   Tracks what each pair of tapes produced.")

(defvar *rxn-queue* (make-array 2000 :initial-element nil)
  "Ring buffer of recent reaction keys for window eviction.")

(defvar *rxn-queue-pos* 0)

(defun reset-rxn-graph! ()
  "Rebuild rxn-queue at current *rxn-window-size*. Call after genome sets window."
  (setf *rxn-graph*     (make-hash-table :test 'equal)
        *rxn-queue*     (make-array *rxn-window-size* :initial-element nil)
        *rxn-queue-pos* 0))

(defun record-reaction! (ha hb hout-a)
  "Record reaction (ha,hb) → hout-a in the sliding window graph."
  (let ((key (cons ha hb)))
    ;; Evict oldest entry if window full
    (let ((old (aref *rxn-queue* *rxn-queue-pos*)))
      (when old (remhash old *rxn-graph*)))
    ;; Add new entry
    (setf (gethash key *rxn-graph*) hout-a)
    (setf (aref *rxn-queue* *rxn-queue-pos*) key)
    (setf *rxn-queue-pos* (mod (1+ *rxn-queue-pos*) *rxn-window-size*))))

(defun find-cycles (max-depth)
  "Search reaction graph for cycles of length 2..max-depth.
   Returns list of (cycle-length start-hash) for each cycle found.
   A cycle means: starting from hash H, following reactions leads back to H."
  (let ((cycles nil)
        (all-hashes (let ((h (make-hash-table)))
                      (maphash (lambda (k v)
                                 (setf (gethash (car k) h) t)
                                 (setf (gethash (cdr k) h) t)
                                 (setf (gethash v h) t))
                               *rxn-graph*)
                      h)))
    (maphash
     (lambda (start-hash _)
       (declare (ignore _))
       ;; DFS from start-hash up to max-depth steps
       (labels ((dfs (current depth visited)
                  (when (<= depth max-depth)
                    ;; Check all reactions where current is an input
                    (maphash
                     (lambda (k v)
                       (when (or (= (car k) current)
                                 (= (cdr k) current))
                         (let ((next v))
                           (cond
                             ;; Found cycle back to start
                             ((= next start-hash)
                              (pushnew (list depth start-hash) cycles
                                       :test #'equal))
                             ;; Continue DFS if not visited
                             ((not (member next visited))
                              (dfs next (1+ depth) (cons next visited)))))))
                     *rxn-graph*))))
         (dfs start-hash 1 (list start-hash))))
     all-hashes)
    cycles))

(defun scc-rxn-graph ()
  "Iterative Tarjan SCC on *rxn-graph*.
   Returns (n-components largest-scc-size spanning-fraction).
   Uses explicit work-stack to avoid call-stack overflow on large graphs."
  (when (zerop (hash-table-count *rxn-graph*))
    (return-from scc-rxn-graph (values 0 0 0.0)))
  ;; Collect unique nodes, assign integer IDs
  (let* ((node->id (make-hash-table))
         (id->node (make-array 6000 :initial-element nil :adjustable t))
         (n-nodes  0))
    (maphash (lambda (k v)
               (dolist (h (list (car k) (cdr k) v))
                 (unless (gethash h node->id)
                   (setf (gethash h node->id) n-nodes)
                   (when (>= n-nodes (length id->node))
                     (adjust-array id->node (* 2 (length id->node)) :initial-element nil))
                   (setf (aref id->node n-nodes) h)
                   (incf n-nodes))))
             *rxn-graph*)
    (when (zerop n-nodes)
      (return-from scc-rxn-graph (values 0 0 0.0)))
    ;; Build adjacency as vector of lists (integer IDs)
    (let ((fwd (make-array n-nodes :initial-element nil)))
      (maphash (lambda (k v)
                 (let ((ia (gethash (car k) node->id))
                       (ib (gethash (cdr k) node->id))
                       (iv (gethash v       node->id)))
                   (pushnew iv (aref fwd ia))
                   (pushnew iv (aref fwd ib))))
               *rxn-graph*)
      ;; Iterative Tarjan using explicit work stack
      ;; Each frame: (node . remaining-neighbors)
      (let ((index    (make-array n-nodes :initial-element -1))
            (lowlink  (make-array n-nodes :initial-element 0))
            (on-stack (make-array n-nodes :initial-element nil))
            (counter  (list 0))
            (s        nil)   ; Tarjan stack (node IDs)
            (work     nil)   ; work stack: (node . neighbor-list-remaining)
            (sccs     nil))
        (dotimes (start n-nodes)
          (when (= (aref index start) -1)
            ;; Push initial frame
            (push (cons start (aref fwd start)) work)
            (setf (aref index   start) (car counter)
                  (aref lowlink start) (car counter))
            (incf (car counter))
            (push start s)
            (setf (aref on-stack start) t)
            ;; Process work stack
            (loop while work do
              (let* ((frame (car work))
                     (v     (car frame))
                     (nbrs  (cdr frame)))
                (if nbrs
                    (let ((w (car nbrs)))
                      (setf (cdr frame) (cdr nbrs))
                      (cond
                        ((= (aref index w) -1)
                         ;; Tree edge — push new frame
                         (setf (aref index   w) (car counter)
                               (aref lowlink w) (car counter))
                         (incf (car counter))
                         (push w s)
                         (setf (aref on-stack w) t)
                         (push (cons w (aref fwd w)) work))
                        ((aref on-stack w)
                         ;; Back edge
                         (setf (aref lowlink v)
                               (min (aref lowlink v) (aref index w))))))
                    ;; Done with v — pop frame, update parent lowlink
                    (progn
                      (pop work)
                      (when work
                        (let ((parent (car (car work))))
                          (setf (aref lowlink parent)
                                (min (aref lowlink parent) (aref lowlink v)))))
                      ;; Root of SCC?
                      (when (= (aref lowlink v) (aref index v))
                        (let ((scc nil))
                          (loop
                            (let ((w (pop s)))
                              (setf (aref on-stack w) nil)
                              (push w scc)
                              (when (= w v) (return))))
                          (push scc sccs)))))))))
        (let* ((sizes   (mapcar #'length sccs))
               (largest (if sizes (reduce #'max sizes) 0))
               (span    (/ (float largest) n-nodes)))
          (values (length sccs) largest span))))))

(defun count-cycles-fast ()
  "Fast cycle detection: look for 2-cycles (mutual catalysis).
   A 2-cycle: output of (A,B) is also an input that produces something
   in the original input set.
   Returns count of 2-cycles found."
  (let ((outputs (make-hash-table))
        (inputs  (make-hash-table))
        (cycles  0))
    (maphash (lambda (k v)
               (setf (gethash v outputs) t)
               (setf (gethash (car k) inputs) t)
               (setf (gethash (cdr k) inputs) t))
             *rxn-graph*)
    (maphash (lambda (k v)
               (when (gethash v inputs)
                 (maphash (lambda (k2 v2)
                            (when (and (or (= (car k2) v) (= (cdr k2) v))
                                       (or (= v2 (car k)) (= v2 (cdr k))))
                              (incf cycles)))
                          *rxn-graph*)))
             *rxn-graph*)
    (floor cycles 2)))

;;; ============================================================
;;; V9 EVOLVABLE INTERACTION PARAMETERS
;;; ============================================================

(defparameter *n-concat* 2
  "How many tapes to concatenate per interaction. 2=BFF, 3=triplet.")

(defparameter *split-point* nil
  "Where to split output back into tape-a. nil = L (symmetric BFF default).
   Integer = asymmetric: tape-a gets first *split-point* symbols,
   tape-b gets the rest (truncated/padded to L).")

(defparameter *birth-death-mode* :symmetric
  "How outputs replace inputs after interaction.
   :symmetric  — both tapes overwritten (BFF, zero-sum)
   :asymmetric — tape-a survives unchanged if its half matches pre-interaction;
                 tape-b always replaced
   :net-growth — if output-a = input-a exactly, tape-b is replaced by a 2nd copy")

(defparameter *pad-mode* :random
  "How to pad output when serialized result shorter than n-concat*L.
   :random  — fill with random symbols (BFF default)
   :repeat  — tile the output
   :zero    — fill with :I (identity, neutral)")

(defparameter *extra-combinators* nil
  "Additional combinator symbols beyond S/K/I.
   nil  — pure SKI
   :W   — add W combinator (W x y → x y y, direct duplication)
   :B   — add B combinator (B x y z → x (y z), composition)
   :WB  — add both W and B")


;;; INTERACT
;;; ============================================================

(defun pad-to! (result total-len start)
  "Fill result from START to TOTAL-LEN using *pad-mode*."
  (case *pad-mode*
    (:random (loop for i from start below total-len
                   do (setf (aref result i) (rand-sym))))
    (:repeat (when (> start 0)
               (loop for i from start below total-len
                     do (setf (aref result i)
                              (aref result (mod (- i start) start))))))
    (:zero   (loop for i from start below total-len
                   do (setf (aref result i) :I)))))

(defun interact! (tape-a tape-b)
  (incf *total-interactions*)
  (let* ((L       *L*)
         (nc      *n-concat*)               ; how many tapes to concat
         (out-len (* nc L))                 ; total output length
         (concat  (make-array out-len))
         (sa      (t-syms tape-a))
         (sb      (t-syms tape-b)))
    ;; Concatenate nc tapes (cycle a/b for simplicity; nc=2 is normal BFF)
    (dotimes (i L) (setf (aref concat i) (aref sa i)))
    (dotimes (i L) (setf (aref concat (+ L i)) (aref sb i)))
    (when (> nc 2)                           ; triplet: repeat tape-a at end
      (dotimes (i L) (setf (aref concat (+ (* 2 L) i)) (aref sa i))))

    (let* ((tree (parse-syms concat 0 out-len))
           (ops  (reduce-by-pressure! tree)))
      (measure-catalysis! ops out-len)
      (incf *total-ops* ops)
      (incf *window-ops* ops)

      (let* ((flat    (serialize tree))
             (n-flat  (length flat))
             (result  (make-array out-len :initial-element :I))
             ;; Split point: where tape-a ends in the output
             (split   (or *split-point* L)))
        ;; Fill result from serialized output
        (loop for sym in flat
              for i from 0 below out-len
              do (setf (aref result i) sym))
        ;; Pad remainder
        (when (< n-flat out-len)
          (pad-to! result out-len n-flat))

        (let* ((new-a   (make-array L))
               (new-b   (make-array L))
               (new-gen (1+ (max (t-gen tape-a) (t-gen tape-b))))
               (ha      (tape-hash tape-a))
               (hb      (tape-hash tape-b)))
          ;; Slice output → tape-a gets [0..split), tape-b gets [split..split+L)
          (dotimes (i L)
            (let ((ai (mod i L))
                  (bi (mod (+ split i) out-len)))
              (setf (aref new-a ai) (aref result (min ai (1- out-len))))
              (setf (aref new-b i)  (aref result (min bi (1- out-len))))))

          ;; Birth/death mode
          (case *birth-death-mode*
            (:symmetric
             ;; Both tapes overwritten — BFF default, zero-sum
             (setf (t-syms tape-a) new-a
                   (t-ops  tape-a) (+ (t-ops tape-a) ops)
                   (t-gen  tape-a) new-gen
                   (t-syms tape-b) new-b
                   (t-ops  tape-b) (+ (t-ops tape-b) ops)
                   (t-gen  tape-b) new-gen))
            (:asymmetric
             ;; Tape-a (template) preserved if output-a matches it exactly
             ;; Tape-b always updated — directional copy
             (let ((match-a (equalp new-a sa)))
               (unless match-a
                 (setf (t-syms tape-a) new-a
                       (t-ops  tape-a) (+ (t-ops tape-a) ops)
                       (t-gen  tape-a) new-gen))
               (setf (t-syms tape-b) new-b
                     (t-ops  tape-b) (+ (t-ops tape-b) ops)
                     (t-gen  tape-b) new-gen)))
            (:net-growth
             ;; If output-a = input-a (perfect replication), tape-b gets a
             ;; second copy of tape-a — net +1 replicator, not zero-sum
             (let ((self-rep (equalp new-a sa)))
               (setf (t-syms tape-a) new-a
                     (t-ops  tape-a) (+ (t-ops tape-a) ops)
                     (t-gen  tape-a) new-gen)
               (if self-rep
                   ;; Tape-a self-replicated: tape-b becomes another copy
                   (setf (t-syms tape-b) (copy-seq sa)
                         (t-ops  tape-b) (+ (t-ops tape-b) ops)
                         (t-gen  tape-b) new-gen)
                   ;; Normal: tape-b gets its output slice
                   (setf (t-syms tape-b) new-b
                         (t-ops  tape-b) (+ (t-ops tape-b) ops)
                         (t-gen  tape-b) new-gen)))))

          ;; Record reaction
          (let ((hout-a (let ((h 17))
                          (loop for s across (t-syms tape-a)
                                do (setf h (ldb (byte 62 0) (+ (* h 31) (sxhash s)))))
                          h)))
            (record-reaction! ha hb hout-a)))))))

;;; ─── Extra combinator alphabet ───────────────────────────────────────────────


;;; ─── Extra combinator alphabet ───────────────────────────────────────────────

(defun build-alphabet (s-w k-w i-w)
  "Build alphabet vector respecting *extra-combinators*."
  (let ((base (append (make-list s-w :initial-element :S)
                      (make-list k-w :initial-element :K)
                      (make-list i-w :initial-element :I))))
    (case *extra-combinators*
      (:W  (coerce (append base '(:W)) 'vector))
      (:B  (coerce (append base '(:B)) 'vector))
      (:WB (coerce (append base '(:W :B)) 'vector))
      (t   (coerce base 'vector)))))

;;; ============================================================
;;; MEASUREMENT (identical to v3)
;;; ============================================================

(defun tape-hash (tape)
  (let ((h 17))
    (loop for s across (t-syms tape)
          do (setf h (ldb (byte 62 0) (+ (* h 31) (sxhash s)))))
    h))

(defun soup-entropy (tv)
  (let ((counts (make-hash-table)) (n (length tv)))
    (dotimes (i n) (incf (gethash (tape-hash (aref tv i)) counts 0)))
    (let ((H 0.0d0))
      (maphash (lambda (k v)
                 (declare (ignore k))
                 (let ((p (/ (float v 1.0d0) n)))
                   (when (> p 0.0d0) (decf H (* p (log p 2.0d0))))))
               counts)
      (values H (hash-table-count counts)))))

(defun count-replicators (tv &optional (min-count 3))
  (let ((counts (make-hash-table)) (n (length tv)))
    (dotimes (i n) (incf (gethash (tape-hash (aref tv i)) counts 0)))
    (let ((r 0))
      (maphash (lambda (k v) (declare (ignore k)) (when (>= v min-count) (incf r))) counts)
      r)))

(defun top-tapes (tv &optional (n 5))
  (let ((counts (make-hash-table)) (examples (make-hash-table)) (len (length tv)))
    (dotimes (i len)
      (let* ((t1 (aref tv i)) (h (tape-hash t1)))
        (incf (gethash h counts 0))
        (unless (gethash h examples) (setf (gethash h examples) t1))))
    (let ((pairs nil))
      (maphash (lambda (k v) (push (cons k v) pairs)) counts)
      (setf pairs (sort pairs #'> :key #'cdr))
      (loop for (h . cnt) in (subseq pairs 0 (min n (length pairs)))
            collect (list cnt (coerce (t-syms (gethash h examples)) 'list))))))

;;; ============================================================
;;; TOPOLOGY: k-regular random graph
;;; ============================================================

(defun make-adjacency (n-tapes k)
  "Build a k-regular undirected random graph on n-tapes nodes.
   Each node has exactly k neighbors (approximate — random walk ensures near-k).
   Returns a vector of neighbor-lists."
  (let ((adj (make-array n-tapes :initial-element nil)))
    ;; Start: ring lattice (each node connected to k/2 on each side)
    (dotimes (i n-tapes)
      (dotimes (d (floor k 2))
        (let ((j (mod (+ i d 1) n-tapes)))
          (pushnew j (aref adj i))
          (pushnew i (aref adj j)))))
    adj))

(defun make-small-world (n-tapes k rewire-p)
  "Watts-Strogatz small-world: start with ring lattice, rewire each edge
   with probability rewire-p to a random node.
   k must be even. Returns adjacency vector."
  (let ((adj (make-array n-tapes :initial-element nil)))
    ;; Build initial ring lattice
    (dotimes (i n-tapes)
      (loop for d from 1 to (floor k 2) do
        (let ((j (mod (+ i d) n-tapes)))
          (pushnew j (aref adj i))
          (pushnew i (aref adj j)))))
    ;; Rewire
    (dotimes (i n-tapes)
      (loop for d from 1 to (floor k 2) do
        (let ((j (mod (+ i d) n-tapes)))
          (when (< (random 1.0) rewire-p)
            ;; Remove edge i-j, add edge i-k (random k ≠ i)
            (setf (aref adj i) (remove j (aref adj i)))
            (setf (aref adj j) (remove i (aref adj j)))
            (let ((new-j (loop for nj = (random n-tapes)
                               until (and (/= nj i)
                                          (not (member nj (aref adj i))))
                               finally (return nj))))
              (pushnew new-j (aref adj i))
              (pushnew i (aref adj new-j)))))))
    adj))

(defun make-grid-2d (side)
  "2D toroidal grid: side×side nodes, each with 4 neighbors.
   Returns adjacency vector of length side*side."
  (let* ((n (* side side))
         (adj (make-array n :initial-element nil)))
    (dotimes (r side)
      (dotimes (c side)
        (let ((i (+ (* r side) c)))
          (let ((neighbors (list (+ (* r side) (mod (1+ c) side))   ; right
                                 (+ (* r side) (mod (1- c) side))   ; left
                                 (+ (* (mod (1+ r) side) side) c)   ; down
                                 (+ (* (mod (1- r) side) side) c)   ; up
                                 )))
            (setf (aref adj i) neighbors)))))
    adj))

;;; ============================================================
;;; ADAPTIVE TOPOLOGY — RAF-driven edge rewiring
;;; ============================================================

(defparameter *rewire-high-threshold* 1.5
  "RAF score multiplier above mean to gain a neighbor (genome-evolvable).")

(defparameter *rewire-low-threshold* 0.5
  "RAF score multiplier below mean to shed a neighbor (genome-evolvable).")

;;; ============================================================
(defun tape-raf-scores (tv n-tapes)
  "Count how often each tape's hash appears as a PRODUCT in the reaction graph.
   Returns a vector of counts, one per tape slot.
   High count = this tape is being catalytically produced = high RAF contribution."
  (let ((scores (make-array n-tapes :initial-element 0))
        ;; Collect all product hashes from the reaction graph
        (product-counts (make-hash-table)))
    (maphash (lambda (key val)
               (declare (ignore key))
               (incf (gethash val product-counts 0)))
             *rxn-graph*)
    ;; Map product hashes back to tape slots
    (dotimes (i n-tapes)
      (let* ((h (tape-hash (aref tv i)))
             (cnt (gethash h product-counts 0)))
        (setf (aref scores i) cnt)))
    scores))

(defun rewire-topology! (adj tv n-tapes)
  "Adaptive topology rewiring based on RAF contribution.
   High-RAF tapes gain a neighbor. Low-RAF tapes lose a neighbor.
   Maintains min-degree=1, max-degree=n-tapes/4."
  (let* ((scores    (tape-raf-scores tv n-tapes))
         (total     (loop for s across scores sum s))
         (mean      (if (> total 0) (/ (float total) n-tapes) 0.0))
         (max-deg   (max 4 (floor n-tapes 4)))
         (changed   0))
    (dotimes (i n-tapes)
      (let ((score (aref scores i))
            (deg   (length (aref adj i))))
        (cond
          ;; High RAF: gain a new neighbor (try up to 10 random candidates)
          ((and (> score (* *rewire-high-threshold* mean))
                (< deg max-deg))
           (let ((candidate nil))
             (dotimes (_ 10)
               (unless candidate
                 (let ((j (random n-tapes)))
                   (when (and (/= j i) (not (member j (aref adj i))))
                     (setf candidate j)))))
             (when candidate
               (pushnew candidate (aref adj i))
               (pushnew i (aref adj candidate))
               (incf changed))))
          ;; Low RAF: shed a neighbor (keep min degree 1)
          ((and (< score (* *rewire-low-threshold* mean))
                (> deg 1))
           (let ((victim (nth (random deg) (aref adj i))))
             (setf (aref adj i) (remove victim (aref adj i)))
             (setf (aref adj victim) (remove i (aref adj victim)))
             ;; Ensure victim still has at least 1 neighbor
             (when (null (aref adj victim))
               (let ((rescue nil))
                 (dotimes (_ 20)
                   (unless rescue
                     (let ((j (random n-tapes)))
                       (when (and (/= j victim) (/= j i))
                         (setf rescue j)))))
                 (when rescue
                   (pushnew rescue (aref adj victim))
                   (pushnew victim (aref adj rescue)))))
             (incf changed)))))
    changed)))

(defun topology-stats (adj n-tapes)
  "Return (values total-edges mean-degree max-degree) for the current adjacency."
  (let ((degrees (loop for i below n-tapes collect (length (aref adj i)))))
    (let ((total (/ (reduce #'+ degrees) 2))
          (mean  (/ (float (reduce #'+ degrees)) n-tapes))
          (mx    (reduce #'max degrees)))
      (values total mean mx))))

;;; ============================================================
;;; MULTI-REGION RUNNER
;;; One soup, many climates. Regions share one tape vector and
;;; one adjacency graph. Inter-region edges exist alongside
;;; intra-region edges. Before each interaction, the source
;;; region's parameters are applied as dynamic bindings.
;;; ============================================================

(defstruct region
  "Parameter set for one climate zone within the unified soup."
  (id           0   :type fixnum)
  (start        0   :type fixnum)   ; first tape index owned by this region
  (end          0   :type fixnum)   ; one past last tape index
  ;; Interaction protocol
  (birth-death  :symmetric)         ; :symmetric :asymmetric :net-growth
  (n-concat     2   :type fixnum)
  (split-point  nil)                ; nil = L, integer = asymmetric split
  (pad-mode     :random)
  (extra-combinators nil)           ; nil :W :B :WB
  ;; Alphabet weights
  (s-weight     3   :type fixnum)
  (k-weight     2   :type fixnum)
  (i-weight     1   :type fixnum)
  ;; Seed: list of symbol vectors to inject at startup
  (seeds        nil))

(defun make-region-alphabet (r)
  "Build alphabet vector from region's s/k/i weights + extra combinators."
  (let ((base (append (make-list (region-s-weight r) :initial-element :S)
                      (make-list (region-k-weight r) :initial-element :K)
                      (make-list (region-i-weight r) :initial-element :I))))
    (case (region-extra-combinators r)
      (:W  (coerce (append base '(:W)) 'vector))
      (:B  (coerce (append base '(:B)) 'vector))
      (:WB (coerce (append base '(:W :B)) 'vector))
      (t   (coerce base 'vector)))))

(defmacro with-region-params (region &body body)
  "Execute BODY with dynamic vars set from REGION's parameter struct."
  `(let ((*birth-death-mode*   (region-birth-death  ,region))
         (*n-concat*           (region-n-concat      ,region))
         (*split-point*        (region-split-point   ,region))
         (*pad-mode*           (region-pad-mode      ,region))
         (*extra-combinators*  (region-extra-combinators ,region))
         (*alphabet*           (make-region-alphabet  ,region)))
     ,@body))

(defun build-multiregion-adj (regions n-tapes k-intra k-inter p-rewire-intra p-cross)
  "Build adjacency for a multi-region soup.
   Within each region: small-world with k-intra neighbors, p-rewire-intra rewiring.
   Between regions: each tape has p-cross probability of one cross-region edge.
   Returns a vector of neighbor-lists of length n-tapes."
  (let ((adj (make-array n-tapes :initial-element nil)))
    ;; Intra-region: ring lattice within each region
    (dolist (r regions)
      (let ((start (region-start r))
            (end   (region-end   r)))
        (let ((size (- end start)))
          (dotimes (di (floor k-intra 2))
            (dotimes (ii size)
              (let* ((i  (+ start ii))
                     (j  (+ start (mod (+ ii di 1) size))))
                (pushnew j (aref adj i))
                (pushnew i (aref adj j))))))))
    ;; Rewire intra-region edges (Watts-Strogatz)
    (dolist (r regions)
      (let ((start (region-start r))
            (end   (region-end   r))
            (size  (- (region-end r) (region-start r))))
        (dotimes (ii size)
          (let ((i (+ start ii)))
            (setf (aref adj i)
                  (loop for j in (aref adj i)
                        collect (if (< (random 1.0) p-rewire-intra)
                                    ;; rewire to random within same region
                                    (let ((new-j (+ start (random size))))
                                      (if (and (/= new-j i)
                                               (not (member new-j (aref adj i))))
                                          new-j j))
                                    j)))))))
    ;; Inter-region: sparse cross-region edges
    (when (> p-cross 0.0)
      (dotimes (i n-tapes)
        (when (< (random 1.0) p-cross)
          ;; Find which region i belongs to
          (let* ((src-region (find-if (lambda (r)
                                        (and (>= i (region-start r))
                                             (< i (region-end r))))
                                      regions))
                 ;; Pick a different region
                 (other-regions (remove src-region regions))
                 (dst-region (when other-regions
                               (nth (random (length other-regions)) other-regions))))
            (when dst-region
              (let ((j (+ (region-start dst-region)
                          (random (- (region-end dst-region)
                                     (region-start dst-region))))))
                (pushnew j (aref adj i))
                (pushnew i (aref adj j))))))))
    adj))

(defun run-multiregion (regions n-epochs
                        &key (k-intra 6) (k-inter 1)
                             (p-rewire-intra 0.1) (p-cross 0.01)
                             (report-every 1000000)
                             (min-replicate-count 2))
  "Run a unified multi-region soup.
   REGIONS: list of REGION structs defining parameter zones.
   Each interaction fires with the SOURCE tape's region parameters.
   Cross-region interactions propagate successful strategies spatially."
  (let* ((n-tapes (reduce #'+ regions :key (lambda (r) (- (region-end r) (region-start r)))))
         (adj     (build-multiregion-adj regions n-tapes k-intra k-inter
                                         p-rewire-intra p-cross))
         ;; Region map: tape-index → region struct (for O(1) lookup)
         (region-map (make-array n-tapes :initial-element nil))
         (tv  (make-array n-tapes))
         (t0  (get-internal-real-time)))

    ;; Build region map
    (dolist (r regions)
      (loop for i from (region-start r) below (region-end r)
            do (setf (aref region-map i) r)))

    ;; Initialize tapes
    (dotimes (i n-tapes)
      (let ((r (aref region-map i)))
        (with-region-params r
          (setf (aref tv i) (fresh-tape)))))

    ;; Seed known quines into regions that have them
    (dolist (r regions)
      (when (region-seeds r)
        (loop for syms in (region-seeds r)
              for i from (region-start r)
              while (< i (region-end r))
              do (let ((arr (make-array *L* :initial-element :I)))
                   (loop for sym across syms for j from 0 while (< j *L*)
                         do (setf (aref arr j) sym))
                   (setf (t-syms (aref tv i)) arr)))))

    (setf *total-ops* 0 *total-interactions* 0 *window-ops* 0)
    (format t "~%╔══════════════════════════════════════════════════╗~%")
    (format t "║  SKI SOUP v10 — MULTI-REGION  (~D regions, ~D tapes) ║~%"
            (length regions) n-tapes)
    (format t "╚══════════════════════════════════════════════════╝~%")
    (format t "p-cross=~,3F  k-intra=~D~%~%" p-cross k-intra)
    (dolist (r regions)
      (format t "  Region ~D: tapes ~D-~D  bd=~A  extra=~A  seeds=~D~%"
              (region-id r) (region-start r) (1- (region-end r))
              (region-birth-death r) (region-extra-combinators r)
              (length (region-seeds r))))
    (format t "~%")
    (force-output)

    ;; ── Main loop ──────────────────────────────────────────────
    (loop for epoch from 1 to n-epochs do
      (let* ((i         (random n-tapes))
             (neighbors (aref adj i)))
        (when neighbors
          (let* ((j      (nth (random (length neighbors)) neighbors))
                 ;; Use SOURCE region's parameters for this interaction
                 (src-r  (aref region-map i)))
            (with-region-params src-r
              (interact! (aref tv i) (aref tv j))))))

      (when (zerop (mod epoch report-every))
        (let* ((elapsed (/ (- (get-internal-real-time) t0)
                           (float internal-time-units-per-second)))
               (rate    (/ epoch elapsed))
               (ops-per-int (if (> *total-interactions* 0)
                                (/ (float *window-ops*) report-every)
                                0.0)))
          (setf *window-ops* 0)
          (multiple-value-bind (H unique) (soup-entropy tv)
            (let* ((ctx (list :epoch epoch :tv tv :n-tapes n-tapes
                              :ops-per-int ops-per-int :rate rate
                              :H H :unique unique :min-rep min-replicate-count)))
              (setf *catalysis-events* 0 *catalysis-samples* 0)
              (format t "~A~%" (render-epoch-line ctx))
              ;; Per-region quine counts
              (let ((o (make-array *L* :initial-element :S)))
                (dolist (r regions)
                  (let ((qcount 0))
                    (loop for i from (region-start r) below (region-end r)
                          do (when (equalp (t-syms (aref tv i)) o)
                               (incf qcount)))
                    (format t "  R~D(~A): ~D/~D quines~%"
                            (region-id r) (region-birth-death r)
                            qcount (- (region-end r) (region-start r))))))
              (dolist (entry (top-tapes tv 5))
                (format t "  ~3Dx  ~{~A~^ ~}~%" (first entry) (second entry)))
              (force-output))))))

    (format t "~%═══ FINAL ═══~%")
    (multiple-value-bind (H unique) (soup-entropy tv)
      (format t "H=~,4F  Unique=~D/~D~%" H unique n-tapes))
    (multiple-value-bind (n-sccs scc-size scc-span)
        (scc-rxn-graph)
      (format t "SCC: ~D components  largest=~D  spanning=~,1F%%  cycles=~D~%~%"
              n-sccs scc-size (* 100.0 scc-span) (count-cycles-fast)))
    (dolist (entry (top-tapes tv 10))
      (format t "  ~4Dx  ~{~A~^ ~}~%" (first entry) (second entry)))
    tv))

;;; ============================================================
;;; SPATIAL RUNNER
;;; ============================================================

(defun run-spatial (n-tapes n-epochs adj
                   &key (report-every 250000)
                        (min-replicate-count 3)
                        (topology-name "spatial")
                        (seed-tapes nil))
  "Run the BFF SKI soup with spatial interaction topology.
   adj: vector of neighbor-lists, length = n-tapes.
   seed-tapes: optional list of symbol lists to inject at startup
               (transduction from other manifolds).  Each entry is
               a list of keyword symbols, e.g. '(:S :K :I :S ...)."
  (setf *total-ops* 0 *total-interactions* 0 *window-ops* 0)

  (format t "~%╔══════════════════════════════════════════════════╗~%")
  (format t "║  SKI SOUP v8 — ~A (L=~D) ║~%" topology-name *L*)
  (format t "╚══════════════════════════════════════════════════╝~%")
  (format t "~%Tapes: ~D  L: ~D  Epochs: ~D  PressureScale: ~,1F  Seeds: ~D~%~%"
          n-tapes *L* n-epochs *pressure-scale* (length seed-tapes))

  (let ((tv (make-array n-tapes))
        (t0 (get-internal-real-time)))
    (dotimes (i n-tapes) (setf (aref tv i) (fresh-tape)))
    ;; Inject seed tapes from other manifolds (transduction)
    (when seed-tapes
      (loop for syms in seed-tapes
            for i from 0
            while (< i n-tapes)
            do (let ((tape (fresh-tape))
                     (arr  (make-array *L* :initial-element :I)))
                 (loop for sym in syms
                       for j from 0
                       while (< j *L*)
                       do (setf (aref arr j) sym))
                 (setf (t-syms tape) arr)
                 (setf (aref tv i) tape))))

    (multiple-value-bind (H unique) (soup-entropy tv)
      (format t "E        0 | H=~,3F u=~D/~D | ops/int=~,3F | reps=~D~%"
              H unique n-tapes 0.0 0))
    (force-output)

    (loop for epoch from 1 to n-epochs do
      ;; Pick a random node, interact with a random neighbor
      (let* ((i (random n-tapes))
             (neighbors (aref adj i)))
        (when neighbors
          (let ((j (nth (random (length neighbors)) neighbors)))
            (interact! (aref tv i) (aref tv j)))))

      (when (zerop (mod epoch report-every))
        (let* ((elapsed (/ (- (get-internal-real-time) t0)
                           (float internal-time-units-per-second)))
               (rate (/ epoch elapsed))
               (ops-per-int (if (> *total-interactions* 0)
                                (/ (float *window-ops*) report-every)
                                0.0)))
          (setf *window-ops* 0)
          ;; ── Adaptive topology rewiring ──
          (rewire-topology! adj tv n-tapes)
          (multiple-value-bind (topo-edges topo-mean topo-max)
              (topology-stats adj n-tapes)
            (multiple-value-bind (H unique) (soup-entropy tv)
              (let* ((ctx (list :epoch epoch :tv tv :n-tapes n-tapes
                              :ops-per-int ops-per-int :rate rate
                              :H H :unique unique :min-rep min-replicate-count))
                     (topo-str (format nil "edges=~D deg=~,1F/~D"
                                       topo-edges topo-mean topo-max)))
                (setf *catalysis-events* 0 *catalysis-samples* 0)
                (format t "~A | ~A~%" (render-epoch-line ctx) topo-str)
                ;; Always show top 5 — reveal what's persisting below the threshold
                (dolist (entry (top-tapes tv 5))
                  (format t "  ~3Dx  ~{~A~^ ~}~%" (first entry) (second entry)))
                (force-output)))))))

    (let* ((elapsed (/ (- (get-internal-real-time) t0)
                       (float internal-time-units-per-second)))
           (rate (/ n-epochs elapsed)))
      (format t "~%═══ FINAL ═══~%")
      (multiple-value-bind (H unique) (soup-entropy tv)
        (format t "H=~,4F  Unique=~D/~D  TotalOps=~D  Rate=~,0F/s~%"
                H unique n-tapes *total-ops* rate))
      (format t "~%Top 10 tapes:~%")
      (dolist (entry (top-tapes tv 10))
        (format t "  ~4Dx  ~{~A~^ ~}~%" (first entry) (second entry)))
      tv)))

;;; ============================================================
;;; MAIN ENTRY POINTS
;;; ============================================================

(defun run-grid (&optional (n-epochs 10000000))
  "32×32 2D toroidal grid, 4 neighbors each."
  (let ((adj (make-grid-2d 32)))
    (run-spatial 1024 n-epochs adj
                 :topology-name "2D Grid 32×32 (k=4)"
                 :report-every 250000)))

(defun run-small-world (&optional (n-epochs 10000000))
  "Small-world: k=6 ring with 10% rewiring (Watts-Strogatz)."
  (let ((adj (make-small-world 1024 6 0.1)))
    (run-spatial 1024 n-epochs adj
                 :topology-name "Small-World (k=6, p=0.1)"
                 :report-every 250000)))

(defun main ()
  "Default: small-world topology — best balance of local clustering + global reach."
  (run-small-world))
