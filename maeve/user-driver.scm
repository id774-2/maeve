(use gauche.parseopt)
(use maeve.compiler.intermediate-language-util)
(use maeve.compiler.intermediate-language-instance)
(use maeve.compiler.middle-end)
(use maeve.compiler.back-end)
(use maeve.compiler.maeve-driver)

(define (main args)
  (let-args (cdr args)
      ((opt:debug?     "d|debug" #f)
       (opt:dont-link? "S")
       (opt:arch       "a|arch=s" (gauche-architecture))
       (else (option . _)  (error "unrecognized option:" option))
       . input-files)
    (debug? opt:debug?)
    (let ((inputs (append
		   (directory-list
		    (build-path (current-directory) "lib" "maeve")
		    :children? #t :add-path? #t
		    :filter (lambda (e) (not (string-suffix? "~" e))))
		   input-files))
	  (compile-for
	   (case/equal
	    (take* (string-split opt:arch #[-_ ]) 2)
	    ((("x86" "64"))
	     compile-for-x86-64)
	    ((("x86") ("x86" "32") ("i686" "pc"))
	     compile-for-x86-32)
	    (else (error "Unsupported architecture :" opt:arch)))))
      (when-debug
       (format (current-error-port) "input-files : ~s\n" inputs))
      (compile-for
       (cut link opt:dont-link?
	    (map (compose compile file->sexp-list)
		 inputs)))
      (process-wait-any #t))))
