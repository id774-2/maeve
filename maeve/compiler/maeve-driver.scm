(define-module maeve.compiler.maeve-driver
  (use gauche.vport)
  (use gauche.uvector)
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (use maeve.compiler.middle-end)
  (use maeve.compiler.back-end)
  (export-all))

(select-module maeve.compiler.maeve-driver)

(define (make-iport-from-many-source open-iport inputs . opt-buffer-size)
  (define buffer-size (get-optional opt-buffer-size 0))
  (make <buffered-input-port>
    :buffer-size buffer-size
    :fill
    (let ((pre-size buffer-size) (p (open-input-string "(")))
      (lambda (v)
	(u8vector-fill! v 0 0 pre-size)
	(let1 i (read-block! v p)
	  (when (or (eqv? 0 i) (eof-object? i))
	    (set! p 
		  (cond
		   ((null? inputs)
		    (set! inputs #f)
		    (open-input-string ")"))
		   ((pair? inputs)
		    (open-iport (pop! inputs)))
		   (else (open-input-string ""))))
	    (set! i (read-block! v p)))
	  i)))))

(define (compile in)
  (let* ((x (scheme->mir in))
	 (omn
	  (cond
	   ((cunit:modules-of* x)
	    pair? =>
	    (lambda (xs)
	      (symbol-join
	       (map mod:name-of xs)
	       "+")))
	   (else (symbol-append "noname"(hash x)))))
	 (_ (when-debug (il->graphviz* #`",|omn|-1" x)))
	 (y (normalize&reduce-graph omn x)))
    (when-debug (il->graphviz* #`",|omn|-3" y))
    (with-output-to-mir-file
     omn (pretty-print y :use-global-table? #t))
    omn))

(define (link dont-link? omns)
  (define (%write-tree xs port)
    (let loop ((xs xs))
      (case/pred
       xs
       (pair?
	(loop (car xs))
	(loop (cdr xs)))
       ((not undefined? eof-object? null?))
       (else (display xs port)))))
  (let* ((cunits
	  (flat-1
	   (port->sexp-list
	    (make-iport-from-many-source
	     open-input-file (map omn->mir-file omns)))))
	 (*definitions* (make-hash-table 'eqv?))
	 (main-unit
	  (cond
	   ((filter-map
	     (lambda (x)
	       (and (cunit:entry-point-of x) x))
	     cunits)
	    length=1? => car)
	   (else
	    (error "link inputs has too many/few entry points : " omns))))
	 (main-init (make-label :name 'main-init)))
    (receive (%modules %large-consts %es %inits)
	(filter-append-map4
	 (lambda (x)
	   (decompose-cunit x)

	   (hash-table-for-each
	    definitions (cut hash-table-put! *definitions* <> <>))

	   (values modules large-consts es
		   (and-let* ((x (cunit:init-point-of x)))
		     (list (make-call :proc (make-mem :base x))))))
	 cunits)
      (cunit:slot-set!*
       main-unit
       :init-point main-init :definitions *definitions*
       :modules %modules :large-consts %large-consts
       :es `(,(%make-deflabel
	       main-init (make-lmd :es (list (make-block :es %inits))))
	     ,@(append-map1 cunit:es-of cunits))))
    (when-debug
     (debug:il:pp/ss "pre compile-2" main-unit))
    (let* ((main-entry-name
	    (cond
	     ((mod:name-of*
	       (label:module-of*
		#0=(cunit:entry-point-of main-unit)))
	      => identity)
	     (else
	      (error "invalid : entry point of main-unit :" #0#))))
	   (x
	    (normalize&reduce-graph
	     #f
	     (change-syntax-level:medium->low 
	      register-allocation-with-no-register
	      proc-parameter-allocation:stack
	      main-unit)))
	   (_ (when-debug (debug:il:pp/ss "in compile-2-1" x)))
	   (y (low-level-code->x86+x86-64 x)))
      (call-with-output-asm-file
       main-entry-name (cut %write-tree y <>))
      (unless dont-link?
	(run-process
	 `("gcc"
	   "-o" ,main-entry-name
	   ,(omn->asm-file main-entry-name)))))))

(provide "maeve/compiler/maeve-driver")
