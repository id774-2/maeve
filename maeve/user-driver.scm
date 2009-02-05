(use gauche.parseopt)
(use maeve.compiler.intermediate-language-util)
(use maeve.compiler.intermediate-language-instance)
(use maeve.compiler.middle-end)
(use maeve.compiler.back-end)
(use maeve.compiler.maeve-driver)

(use util.toposort)

(define (sort-modules crs)
  (reverse!
   (topological-sort
    (map
     (lambda (cr)
       (decompose-compile-result cr)
       (cons omn imported-modules))
     crs))))

(define (main args)
  (let-args (cdr args)
      ((opt:debug?     "d|debug=s" "")
       (opt:stop "S=s")
       (opt:arch       "a|arch=s" (gauche-architecture))
       (else (option . _)  (error "unrecognized option:" option))
       . main-files)
    (for-each
     (parse-debug-option)
     (string-split opt:debug? #[, ]))
    (let ((inputs (append
		   
		   main-files))
	  (compile-for
	   (case/equal
	    (take* (string-split opt:arch #[-_ ]) 2)
	    ((("x86" "64"))
	     compile-for-x86-64)
	    ((("x86") ("x86" "32") ("i686" "pc"))
	     compile-for-x86-32)
	    (else (error "Unsupported architecture :" opt:arch)))))
      (define allow-link? #t)
      (define (compile-files proc files)
	(fold
	 (lambda (i p)
	   (cond
	    ((compile (file->sexp-list i) opt:stop)
	     => (cut proc <> p))
	    (else (set! allow-link? #f) p)))
	 '()
	 files))
      (when-debug
       (format (current-error-port) "input-files : ~s\n" inputs))
      (compile-for
       (lambda ()
	 ;; compile all library files
	 (compile-files
	  cons
	  (directory-list
	   (build-path (current-directory) "lib" "maeve")
	   :children? #t :add-path? #t
	   :filter (lambda (e) (not (string-suffix? "~" e)))))
	 (let1 main-omns
	     ;; compile all main files
	     (sort-modules
	      (compile-files cons main-files))
	   (when allow-link?
	     (link main-omns opt:stop)))))
      (process-wait-any #t))))
