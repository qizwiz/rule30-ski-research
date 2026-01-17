;;; surface.el --- Programmable Surface Layer for Emacs (Minimal)

;;;; Core Concept:
;;;; Every interactable element becomes visible and touchable.
;;;; State persisted in Redis. Touch = action. MCP-Lisp integration.
;;;; Pure Emacs Lisp + Redis CLI. No HTTP, no WebSocket.

(require 'cl-lib)
(require 'imenu)
(require 'recentf)

;;; Configuration
(defvar surface:*redis-host* "localhost")
(defvar surface:*redis-port* "6379")
(defvar surface:*buffer-name* "* Surface *")
(defvar surface:*elements* (make-hash-table :test 'equal))
(defvar surface:*visible* nil)
(defvar surface:*update-timer* nil)

;;; Element Types
(defvar surface:*types*
  '((buffer :icon "📄" :actions (switch kill rename))
    (file :icon "📁" :actions (open edit delete))
    (function :icon "ƒ" :actions (edit evaluate xref))
    (variable :icon "≡" :actions (set describe xref))
    (mode :icon "⚙️" :actions (describe customize))
    (project :icon "📦" :actions (magit compile))))

(cl-defstruct surface-element
  id type name buffer file line context actions)

;;; Redis CLI Wrapper
(defun surface:redis (&rest args)
  "Execute redis-cli command"
  (let ((cmd (format "redis-cli -h %s -p %s %s"
                     surface:*redis-host*
                     surface:*redis-port*
                     (string-join args " "))))
    (string-trim (shell-command-to-string cmd))))

(defun surface:redis-set (key value)
  (surface:redis "SET" key (shell-quote-argument value)))

(defun surface:redis-get (key)
  (surface:redis "GET" key))

(defun surface:redis-hset (hash field value)
  (surface:redis "HSET" hash field (shell-quote-argument value)))

(defun surface:redis-hget (hash field)
  (surface:redis "HGET" hash field))

(defun surface:redis-hdel (hash field)
  (surface:redis "HDEL" hash field))

(defun surface:redis-keys (pattern)
  (let ((result (surface:redis "KEYS" pattern)))
    (when (and result (not (string= result "")))
      (delete "" (split-string result "\n")))))

(defun surface:redis-publish (channel message)
  (surface:redis "PUBLISH" channel (shell-quote-argument message)))

;;; Detect Elements
(defun surface:detect ()
  "Detect all interactable elements"
  (clrhash surface:*elements*)
  (surface:redis "DEL" "surface:elements")
  
  ;; Buffers
  (dolist (buf (buffer-list))
    (let ((name (buffer-name buf)))
      (unless (string-match-p "^*" name)
        (let ((el (make-surface-element
                   :id (format "buf:%s" name)
                   :type 'buffer
                   :name name
                   :buffer name
                   :file (buffer-file-name buf)
                   :line 1
                   :context nil
                   :actions (alist-get 'buffer surface:*types*))))
          (surface:persist el)))))
  
  ;; Imenu functions
  (condition-case nil
      (progn
        (imenu--make-index-alist)
        (dolist (item imenu--index-alist)
          (when (consp item)
            (let* ((name (car item))
                   (pos (cdr item))
                   (el (make-surface-element
                        :id (format "fn:%s" name)
                        :type 'function
                        :name name
                        :buffer (buffer-name)
                        :file (buffer-file-name)
                        :line (when (number-or-marker-p pos) (line-number-at-pos pos))
                        :context nil
                        :actions (alist-get 'function surface:*types*))))
            (surface:persist el)))))
    (error nil)))

;;; Persist to Redis
(defun surface:persist (el)
  "Persist element to local hash and Redis"
  (setf (gethash (surface-element-id el) surface:*elements*) el)
  (surface:redis-hset "surface:elements" 
                      (surface-element-id el)
                      (format "%s %s %s" 
                              (surface-element-type el)
                              (surface-element-name el)
                              (or (surface-element-buffer el) ""))))

;;; Render Surface Buffer
(defun surface:render ()
  "Render the surface"
  (when (not (get-buffer surface:*buffer-name*))
    (generate-new-buffer surface:*buffer-name*))
  (with-current-buffer (get-buffer surface:*buffer-name*)
    (let ((inhibit-read-only t))
      (erase-buffer)
      (insert "┌────────────────────────────────────────────────────────┐\n")
      (insert "│           Emacs Programmable Surface Layer            │\n")
      (insert "│         Visual • Persistent • Interactive • MCP       │\n")
      (insert "├────────────────────────────────────────────────────────┤\n")
      (insert "│ Type  │ Name                        │ Buffer     │ Line │\n")
      (insert "├────────────────────────────────────────────────────────┤\n")
      
      ;; Render elements
      (maphash (lambda (id el)
                 (let* ((type (surface-element-type el))
                        (type-def (alist-get type surface:*types*))
                        (icon (plist-get type-def :icon)))
                   (insert (format "│ %s     │ %-26s │ %-10s │ %-4s │\n"
                                   (or icon " ")
                                   (substring (surface-element-name el) 0 (min 26 (length (surface-element-name el))))
                                   (or (surface-element-buffer el) "-")
                                   (if (surface-element-line el)
                                       (number-to-string (surface-element-line el))
                                     "-")))))
               surface:*elements*)
      
      (insert "└────────────────────────────────────────────────────────┘\n")
      (insert "\n")
      (insert "Commands: C-c C-c (refresh) | C-c C-q (quit) | RET (action)\n")
      (insert "MCP: C-c C-m invokes MCP-Lisp expression\n"))))

;;; Actions
(defun surface:action (el action)
  "Execute action on element"
  (let ((type (surface-element-type el)))
    (cond
      ((eq action 'switch)
       (when (surface-element-buffer el)
         (switch-to-buffer (surface-element-buffer el))))
      ((eq action 'open)
       (when (surface-element-file el)
         (find-file (surface-element-file el))))
      ((eq action 'magit)
       (magit-status))
      ((eq action 'describe)
       (cond
         ((eq type 'function) (describe-function (intern (surface-element-name el))))
         ((eq type 'variable) (describe-variable (intern (surface-element-name el))))
         ((eq type 'mode) (describe-mode)))))))

;;; MCP-Lisp Integration
(defun surface:mcp ()
  "Invoke MCP-Lisp expression via god-mode-mcp"
  (interactive)
  (let ((expr (read-from-minibuffer "MCP: " "(+ 2 3)")))
    (condition-case err
        (progn
          (load "/Users/jonathanhill/src/mcp-lisp/god-mode-mcp.lisp")
          (let ((result (mcp-eval (car (read-from-string expr)))))
            (message "Result: %s" result)))
      (error
       (message "MCP Error: %s" err)
       (message "Expression: %s" expr)))))

;; Compatibility fallback
(defun surface:mcp-fallback (expr)
  "Fallback MCP evaluation"
  (condition-case err
      (eval (car (read-from-string expr)))
    (error (message "MCP Error: %s" err) nil)))

;;; Toggle
(defun surface:toggle ()
  "Toggle surface visibility"
  (interactive)
  (if surface:*visible*
      (surface:hide)
    (surface:show)))

(defun surface:show ()
  "Show surface"
  (interactive)
  (surface:detect)
  (surface:render)
  (switch-to-buffer surface:*buffer-name*)
  (surface:mode)
  (setf surface:*visible* t)
  (message "Surface visible"))

(defun surface:hide ()
  "Hide surface"
  (interactive)
  (kill-buffer surface:*buffer-name*)
  (setf surface:*visible* nil)
  (message "Surface hidden"))

;;; Auto-refresh
(defun surface:refresh ()
  "Refresh surface"
  (interactive)
  (surface:detect)
  (surface:render)
  (message "Surface refreshed"))

(defun surface:auto-refresh ()
  "Start auto-refresh"
  (when surface:*update-timer*
    (cancel-timer surface:*update-timer*))
  (setf surface:*update-timer*
        (run-with-timer 3 3 #'surface:refresh)))

;;; Major Mode
(define-derived-mode surface:mode special-mode "Surface"
  "Programmable Surface Layer."
  (setq buffer-read-only t)
  (local-set-key (kbd "C-c C-c") #'surface:refresh)
  (local-set-key (kbd "C-c C-q") #'surface:hide)
  (local-set-key (kbd "C-c C-m") #'surface:mcp)
  (local-set-key (kbd "RET") #'surface:handle-at-point))

(defun surface:handle-at-point ()
  "Handle element at point"
  (interactive)
  (message "Point at: %s" (point)))

;;; Quick Commands
(defun surface:buffers ()
  "Show buffers"
  (interactive)
  (surface:detect)
  (surface:show))

(defun surface:functions ()
  "Show functions in current buffer"
  (interactive)
  (surface:detect)
  (surface:show))

;;; Initialize
(defun surface:init ()
  "Initialize surface"
  (message "Surface initializing...")
  (surface:detect)
  (surface:show)
  (surface:auto-refresh)
  (message "Surface ready! C-c C-c to refresh, C-c C-q to hide"))

(provide 'surface)
(message "Surface loaded - M-x surface:init")

;;; surface.el ends here
