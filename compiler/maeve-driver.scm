(define-module maeve.compiler.maeve-driver
  (use gauche.vport)
  (use gauche.uvector)
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (use maeve.compiler.register-allocation)
  (use maeve.compiler.data-flow-analysis)
  (use maeve.compiler.middle-end)
  (use maeve.compiler.back-end)
  (export-all))

(select-module maeve.compiler.maeve-driver)

;; (port->string
;; (make-iport-from-many-source
;;  open-input-string
;;  '("abc" "d" "ef" "ghi")))
;; #?=inputs
;; #?-    ("abc" "d" "ef" "ghi")
;; "(abcdefghi)"

(define (make-iport-from-many-source open-iport inputs . opt-buffer-size)
;;  (define buffer-size (get-optional opt-buffer-size 0))
;;   (make <buffered-input-port>
;;     :buffer-size buffer-size
;;     :fill
;;     (let ((pre-size buffer-size) (p (open-input-string "(")))
;;       (lambda (v)
;; 	(u8vector-fill! v 0 0 pre-size)
;; 	(let1 i (read-block! v p)
;; 	  (when (or (eqv? 0 i) (eof-object? i))
;; 	    (set! p 
;; 		  (cond
;; 		   ((null? inputs)
;; 		    (set! inputs #f)
;; 		    (open-input-string ")"))
;; 		   ((pair? inputs)
;; 		    (open-iport (pop! inputs)))
;; 		   (else (open-input-string ""))))
;; 	    (set! i (read-block! v p)))
;; 	  #?=(u8vector->string v)
;; 	  i))))
  #?=inputs
  (make <virtual-input-port>
    :getc
    (let ((p (open-input-string "(")))
      (lambda ()
	(let1 c (read-char p)
	  (if (eof-object? c)
	    (cond
	     ((null? inputs) (set! inputs #f) #\))
	     ((not inputs) c)
	     (else
	      (set! p (open-iport (pop! inputs)))
	      (read-char p)))
	    c))))))

(define (link omns stop)
  (define (%write-tree xs port)
    (let loop ((xs xs))
      (case/pred
       xs
       (pair?
	(loop (car xs))
	(loop (cdr xs)))
       ((not undefined? eof-object? null?))
       (else (display xs port)))))
  (let/cc escape
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
      (receive (%modules %large-consts %es %inits %imm-type->tag)
	  (filter-append-map5
	   (lambda (x)
	     (decompose-cunit x)

	     (hash-table-for-each
	      definitions (cut hash-table-put! *definitions* <> <>))

	     (values modules large-consts es
		     (and-let* ((x (cunit:init-point-of x)))
		       (list (make-call :proc (make-mem :base x))))
		     (and
		      imm-type->tag
		      (list imm-type->tag))))
	   cunits)
	(cunit:slot-set!*
	 main-unit
	 :init-point main-init :definitions *definitions*
	 :modules %modules :large-consts %large-consts
	 :imm-type->tag
	 (cond
	  ((length=1? %imm-type->tag)
	   (car %imm-type->tag))
	  (else
	   (error "Too many or too few imm-type->tag :" %imm-type->tag)))
	 :imm-type-tag-size
	 (let1 %imm-type-tag-size
	     (filter-map
	      (lambda (x)
		(cunit:imm-type-tag-size-of x))
	      cunits)
	   (cond
	    ((length=1? %imm-type-tag-size)
	     (car %imm-type-tag-size))
	    (else
	     (error "Too many or too few imm-type->tag :" %imm-type->tag))))
	 :es `(,(%make-deflabel
		 main-init (make-lmd :es (list (make-block :es %inits))))
	       ,@(append-map1 cunit:es-of cunits))))
      (when-stop "pre-medium->low" main-unit)
      ;;(debug:il:pp "pre-medium->low extra" main-unit)
      (when #f
       (let* ((%reach (reach main-unit))
	      (chain (make-hash-table 'equal?)))
	 ;;        (hash-table-dump*
	 ;; 	%reach :pre-key-filter il:id :value-filter
	 ;; 	(cut hash-table-map
	 ;; 	     <> (lambda (k v)
	 ;; 		  (cons (il->sexp/ss k) (map il->sexp/ss v)))))
	 (with-output-to-file "tmp/depend.dot"
	   (lambda ()
	     (print "digraph cfg {")
	     (hash-table-for-each
	      %reach
	      (lambda (stm rd)
		(hash-table-for-each
		 rd (lambda (v es)
		      (for-each
		       (lambda (e)
			 (decompose-rd-elm e)
			 (receive (%use _) (%use&kill src)
			   (for-each
			    (lambda (e)
			      (hash-table-push! chain dist (live-elm:var-of e)))
			    %use)))
		       es)))))
	     (let1 memo (make-hash-table 'equal?)
	       (hash-table-for-each
		chain
		(lambda (d ss)
		  (for-each
		   (lambda (s)
		     (unless (hash-table-exists? memo (cons s d))
		       (hash-table-put! memo (cons s d) #t)
		       (format #t "var_~s -> var_~s;\n"
			       (il:id s) (il:id d))))
		   ss))))
	     (print "}")))))
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
	       (rlet1
		x (change-syntax-level:medium->low 
		   register-allocation:primitive-approximation
		   proc-parameter-allocation:register
		   main-unit)
		(with-output-to-file #`"tmp/,main-entry-name"
		  (cut write/ss x))
		;; (debug:il:pp/ss "pre-normalize2" x)
		)))
	     (_ (begin
		  (debug:il:pp "post-normalize2" x)
		  (when-stop "medium->low" x)))
	     (y (low-level-code->x86+x86-64 x)))
	(call-with-output-asm-file
	 main-entry-name (cut %write-tree y <>))
	(flush-all-ports)
	(unless (equal? "pre-link" stop)
	  #?=(run-process
	      #?=`("gcc"
	     "-o" ,main-entry-name
	     ,(omn->asm-file main-entry-name))
	      :wait #t))))))

(provide "maeve/compiler/maeve-driver")
