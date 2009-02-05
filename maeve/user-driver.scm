(use gauche.parseopt)
(use maeve.compiler.intermediate-language-util)
(use maeve.compiler.intermediate-language-instance)
(use maeve.compiler.middle-end)
(use maeve.compiler.back-end)
(use maeve.compiler.maeve-driver)

(define (main args)
  (let-args (cdr args)
      ((opt:debug "d|debug" #f)
       (else (option . _)  (error "unrecognized option:" option))
       . input-files)
    (debug? opt:debug)
    
    (let1 inputs (append
		  (directory-list
		   (build-path (current-directory) "lib" "maeve")
		   :children? #t :add-path? #t
		   :filter (lambda (e) (not (string-suffix? "~" e))))
		  input-files)
      (when-debug
       (format (current-error-port) "input-files : ~s" inputs))
      (link (map (compose compile file->sexp-list)
		 inputs))
      (process-wait-any #t))))
