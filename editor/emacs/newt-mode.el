;; -*- lexical-binding: t; -*-

;; Simple mode for newt, WIP

;; in init.el:

;; (use-package lsp-mode
;;  :hook
;;  ((newt-mode . lsp))
;;
;;  :commands lsp)
;; (add-to-list 'load-path "~/.emacs.d/newt")
;; (require 'newt-mode)
;; (add-to-list 'lsp-language-id-configuration '(newt-mode . "newt"))
;; (lsp-register-client (make-lsp-client
;;                       :new-connection (lsp-stdio-connection '("newt-lsp" "--stdio"))
;;                       :activation-fn (lsp-activate-on "newt")
;;                       :server-id 'newtls))

(require 'rx)

;; Needs a syntax table for the comments
;; so we can't use define-generic-mode
;; which seems to choke on the /- vs --
(defvar newt-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?/ ". 14nb" st)
    (modify-syntax-entry ?- ". 123" st)
    (modify-syntax-entry ?\n ">" st)
    st))

;; TODO flesh this out a bit, although we could
;; also pull in the tree-sitter parser
(defconst newt-font-lock-defaults
  `((
     (,(rx word-start
           (or "module" "import" "data" "record" "where" "let" "in"
               "do"
               "class" "instance"
               "case" "of"
               "=>" "->" "<-" "→") word-end) . 'font-lock-keyword-face))))

(define-derived-mode newt-mode fundamental-mode "Newt"
  :syntax-table newt-syntax-table
  ;; :abbrev-table
  :group 'newt
  (set (make-local-variable 'comment-use-syntax) t)
  (set (make-local-variable 'font-lock-defaults) newt-font-lock-defaults)
  (set (make-local-variable 'comment-start) "--")
  (setq mode-name "newt"))

(add-to-list 'auto-mode-alist '("\\.newt\\'" . newt-mode))

;; No longer use the compiler for errors, but I'll keep a copy for posterity
;;
;; (flycheck-define-checker newt
;;   "A newt syntax checker"
;;   :command ("newt" source-original)
;;   :error-patterns
;;   (
;;    (error line-start "ERROR at " (file-name) ":" line ":" column "--" end-line ":" end-column ":" (message) line-end)
;;    ;; need to grab subsequent lines starting with whitespace..
;;    ;; probably want something other than flycheck for this. Also switch to LSP. :)
;;    (info line-start "INFO at " (file-name) ":" line ":" column "--" end-line ":" end-column ":" (message) line-end)
;;    )
;;   :modes newt-mode)
;; (add-to-list 'flycheck-checkers 'newt)
(provide 'newt-mode)
