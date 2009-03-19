(use gauche.parseopt)
(use maeve.compiler.intermediate-language-util)
(use maeve.compiler.intermediate-language-instance)
(use maeve.compiler.middle-end)
(use maeve.compiler.back-end)
(use maeve.compiler.maeve-driver)

(use util.toposort)

(define (sort-modules crs)
  (let1 ncrs
      (map
       (lambda (cr)
	 (decompose-compile-result cr)
	 (cons omn imported-modules))
       crs)
    (if (null? ncrs)
      '()
      (reverse!
       (topological-sort ncrs)))))

(define (main args)
  (let-args (cdr args)
      ((opt:debug?     "d|debug=s" "")
       (opt:stop       "S|stop=s")
       (opt:arch       "a|arch=s" (gauche-architecture))
       (opt:no-lib?    "no-lib")
       (else (option . _)  (error "unrecognized option:" option))
       . main-files)
    (for-each
     (parse-debug-option)
     (string-split opt:debug? #[, ]))
    (let ((inputs main-files)
	  (compile-for
	   (case/equal
	    (take* (string-split opt:arch #[-_ ]) 2)
	    ((("x86" "64"))
	     compile-for-x86-64)
	    ((("x86") ("x86" "32") ("i686" "pc"))
	     compile-for-x86-32)
	    (else (error "Unsupported architecture :" opt:arch)))))
      (define allow-link? #t)
      (define (compile-files files)
	(filter-map
	 (lambda (i)
	   (rlet1 r (compile-file i opt:stop)
		  (unless r (set! allow-link? #f))))
	 files))
      (when-debug
       (format (current-error-port) "input-files : ~s\n" inputs))
      (compile-for
       (lambda ()
	 ;; compile all library files
;; 	 (unless opt:no-lib?
;; 	   (compile-files
;; 	    (*all-library-files*)))
	 (let1 main-omns
	     ;; compile all main files
	     #?=(sort-modules
	      (compile-files main-files))
	     (when allow-link?
	       (link main-omns opt:stop)))))
      (process-wait-any #t))))

