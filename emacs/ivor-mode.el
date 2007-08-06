(defvar ivor-mode-map
   (let ((map (make-sparse-keymap)))
     (define-key map "\C-j" 'newline-and-indent)
     (define-key map "\C-n" 'ivor-send-to-shell)
     (define-key map "\C-c\C-n" 'ivor-send-all-to-shell)
     (define-key map "\C-c\C-s" 'ivor-start)
     (define-key map "\C-c\C-d" 'ivor-stop)
     (define-key map "\C-c\C-r" 'ivor-restart)
     (define-key map "\C-c\C-u" 'ivor-undo)
     map)
   "Keymap for `ivor-mode'.")

(add-to-list 'auto-mode-alist '("\\.tt\\'" . ivor-mode))

(defvar ivor-mode-syntax-table
   (let ((st (make-syntax-table)))
     (modify-syntax-entry ?{ ". 1" st)
     (modify-syntax-entry ?} ". 4" st)
     (modify-syntax-entry ?- ". 1b2b3" st)
     (modify-syntax-entry ?\n "> b" st)
     st)
   "Syntax table for `ivor-mode'.")

;;;(regexp-opt '("Data" "Rec" "Qed" "Freeze" "Thaw" "Eval" "Check" "Load"
;;;	      "Suspend" "Resume" "Compile" "Repl" "Equality" "Drop"
;;;	      "Primitives" "Forget" "Let" "Axiom" "Focus" "Declare" "Where"))

;;;(regexp-opt '("attack" "claim" "local" "refine" "solve" "fill" "return"
;;;	      "quote" "call" "abandon" "rename" "intro" "intros" "arg"
;;;	      "equiv" "generalise" "dependent" "replace" "axiomatise"
;;;	      "compute" "unfold" "trivial" "by" "induction" "case" 
;;;           "auto" "left" "right" "split" "exists"))

(defconst ivor-font-lock-keywords
  (list '("\\<\\(Axiom\\|C\\(?:heck\\|ompile\\)\\|D\\(?:ata\\|eclare\\|rop\\)\\|E\\(?:quality\\|val\\)\\|F\\(?:o\\(?:cus\\|rget\\)\\|reeze\\)\\|L\\(?:et\\|oad\\)\\|Primitives\\|Qed\\|Re\\(?:c\\|pl\\|sume\\)\\|Suspend\\|Thaw\\|where\\)\\>"
 . font-lock-keyword-face)
        '("a\\(?:bandon\\|rg\\|ttack\\|uto\\|xiomatise\\)\\|by\\|c\\(?:a\\(?:ll\\|se\\)\\|laim\\|ompute\\)\\|dependent\\|e\\(?:quiv\\|xists\\)\\|fill\\|generalise\\|in\\(?:duction\\|tros?\\)\\|l\\(?:eft\\|ocal\\)\\|quote\\|r\\(?:e\\(?:fine\\|name\\|place\\|turn\\)\\|ight\\)\\|s\\(?:olve\\|plit\\)\\|trivial\\|unfold" . font-lock-builtin-face)
	'("<\\([^:]*\\):[^>]*>" . (1 font-lock-string-face keep t))
	'("<\\([^>:]*\\)>" . (1 font-lock-string-face keep t))
	'("^\\([a-zA-Z0-9\\'\\_]+\\)\\s-*:" . (1 font-lock-function-name-face keep t))
	'("^\\([a-zA-Z0-9\\'\\_]+\\)\\s-*=" . (1 font-lock-function-name-face keep t))
	'("Rec\\s-+\\([a-zA-Z0-9\\'\\_]+\\)\\s-*:" . (1 font-lock-function-name-face t t))
	'("\\b\\([a-zA-Z0-9\\'\\_]+\\)\\s-*:" . (1 font-lock-variable-name-face keep t))
	'("\\b\\([a-zA-Z0-9\\'\\_]+\\)\\s-*," . (1 font-lock-variable-name-face keep t))
  )
  "Highlighting for Ivor mode")

;;;(defvar tt-font-lock-keywords
;;;   '(("Data" (1 font-lock-keyword-face)))
;;;   "Keyword highlighting specification for `ivor-mode'.")


;;(defvar tt-imenu-generic-expression
;;   ...)

;;(defvar tt-outline-regexp
;;   ...)

 ;;;###autoload
(define-derived-mode ivor-mode fundamental-mode "Ivor"
   "A major mode for editing Ivor files."
   (set (make-local-variable 'comment-start) "-- ")
   (set (make-local-variable 'comment-start-skip) "#+\\s-*")
   (set (make-local-variable 'font-lock-defaults)
	'(ivor-font-lock-keywords))
   (set (make-local-variable 'indent-line-function) 'ivor-indent-line)
;;   (set (make-local-variable 'imenu-generic-expression)
;;	ivor-imenu-generic-expression)
;;   (set (make-local-variable 'outline-regexp) ivor-outline-regexp)
   )

;;; Indentation
;; 1. Qed line is indented to 0
;; 2. After 'Data' indent each line 4 until a semicolon, or 2 if the line
;;    begins with '|' or '='


(defun ivor-indent-line ()
   "Indent current line of Ivor code."
   (interactive)
   (let ((savep (> (current-column) (current-indentation)))
	 (indent (condition-case nil (max (ivor-calculate-indentation) 0)
		   (error 0))))
     (if savep
	 (save-excursion (indent-line-to indent))
       (indent-line-to indent))))

(defun ivor-calculate-indentation ()
   "Return the column to which the current line should be indented."
   ;; Default is the indentation of the previous line
  (cond 
   ((ivor-isQed) 0)
   ((ivor-first-is "[ \\t]*|") (ivor-under-eq))
   ((ivor-eq-no-semi) 4)
   ((ivor-first-is "[ \\t]*=") 2)
   (t (ivor-get-previous-indentation))
  )
)

(defun ivor-isQed ()
  (save-excursion
    (beginning-of-line)
    (looking-at "Qed")))

(defun ivor-eq-no-semi ()
  (save-excursion
    (forward-line -1)
    (beginning-of-line)
    (looking-at ".*=[^;]*$")))

(defun ivor-under-eq ()
  "Indent to under the = sign on the previous line, or 4 spaces if none"
  (save-excursion
    (forward-line -1)
    (beginning-of-line)
    (let ((this-line (thing-at-point 'line)))
      (let ((eq-point (string-match "=" this-line)))
	(progn (if (eq eq-point nil)
		   2
		 eq-point))))))

(defun ivor-first-is (str)
  (save-excursion
    (beginning-of-line)
    (looking-at str)))

(defun ivor-get-previous-indentation ()
  "Return the indentation of the previous line"
  (save-excursion
    (forward-line -1)
    (current-indentation)))

(defun ivor-send-to-shell ()
  "Read the current line and send it to the shell process, if any"
  (interactive)
  (progn (save-excursion
	   (beginning-of-line)
	   (let* ((this-line (thing-at-point 'line))
	          (chomped (substring this-line 0 (- (length this-line) 1))))
	     (progn (set-buffer (get-buffer "*Ivor*"))
		    (insert chomped)
		    (comint-send-input))))
	 (forward-line 1)
	 (beginning-of-line)
	 )
)

(defun ivor-send-all-to-shell ()
  "Send the buffer up to the current point to the shell process"
  (interactive)
  (let ((contents (buffer-substring 1 (point))))
	(progn (set-buffer (get-buffer "*Ivor*"))
	       (insert contents)
	       (comint-send-input))))

(defvar ivor-shell-exec "jones")
(defvar ivor-shell-sep ";")

(defun set-ivor-shell (executable)
  "Set the Ivor shell executable"
  (interactive "sShell executable: ")
  (setq ivor-shell-exec executable))

(defun set-ivor-sep (sep)
  "Set the Ivor shell command separator"
  (interactive "sShell separator: ")
  (setq ivor-shell-sep sep))

(defun ivor-start ()
  "Start a shell with Ivor in it"
  (interactive)
  (when (not (bufferp (get-buffer "*Ivor*")))
    (progn (shell "*Ivor*")
	   (set-buffer (get-buffer "*Ivor*"))
	   (insert ivor-shell-exec)
	   (comint-send-input))))

(defun ivor-stop ()
  "Stop the Ivor process"
  (interactive)
  (let ((dir (file-name-directory buffer-file-name)))
    (save-current-buffer
      (progn (set-buffer (get-buffer "*Ivor*"))
	     (insert (concat "Drop" ivor-shell-sep))
	     (comint-send-input))))
  (beginning-of-buffer))

(defun ivor-restart ()
  "Restart the Ivor process"
  (interactive)
  (let ((dir (file-name-directory buffer-file-name)))
    (save-current-buffer
      (progn (set-buffer (get-buffer "*Ivor*"))
	     (insert (concat "Drop" ivor-shell-sep))
	     (comint-send-input)
	     (insert (concat "cd " dir "; " ivor-shell-exec))
	     (comint-send-input))))
  (beginning-of-buffer))

(defun ivor-undo-proof ()
  "Send undo command in a proof state."
  (interactive)
  (let ((dir (file-name-directory buffer-file-name)))
    (save-current-buffer
      (progn (set-buffer (get-buffer "*Ivor*"))
	     (insert "Undo;")
	     (comint-send-input))))
  (beginning-of-buffer))

(provide 'ivor)
