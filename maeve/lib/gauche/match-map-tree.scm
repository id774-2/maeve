(define-module maeve.lib.gauche.match-map-tree
  (use util.match)
  (use maeve.lib.gauche.list-util)
  (use maeve.lib.gauche.macro-util)
  (use maeve.lib.gauche.complex-iterator)
  (export-all))

(select-module maeve.lib.gauche.match-map-tree)

(define *components* (make-hash-table 'eqv?))

(define-macro (define-mmt-handlers name . handlers)
  (unless (symbol? name)
    (error "mmt clause name must be symbol, but got :" name))

  (hash-table-put! *components* name handlers)

  ;; (format #t "mmt handler ~s is defined.\n" name)
  )

(define-macro (mmt-match in . handlers)
  `(match
    ,in
    ,@(append-map1
       (lambda (x) (if (pair? x) x (hash-table-get *components* x)))
       handlers)))

(define-mmt-handlers
  mmt:default
  ((x . xs)
   (cons (,loop x) (,loop xs)))
  (else ,self))

(define-macro (limited-match-map-tree-pre-order tree . specs)
  `(let loop ((xs ,tree))
     (match
      xs
      ,@specs
      ((x . xs) (cons (loop x) (loop xs)))
      (x x))))

(define-macro (memorize ht-type proc . rest)
  (let-keywords
   rest ((single-value? #f) (values? #t))
   (when single-value? (set! values? #f))
   (with-gensyms
    (ht result args)
    (define (gen-values result)
      (if values?
	`(apply values ,result)
	result))
    `(let ((,ht (make-hash-table ',ht-type)))
       (lambda ,args
	 (cond
	  ((hash-table-get ,ht ,args #f)
	   => (lambda (,result)
		,(gen-values result)))
	  (else
	   (,(if single-value? 'let1 'receive)
	    ,result (apply ,proc ,args)
	    (hash-table-put! ,ht ,args ,result)
	    ,(gen-values result)))))))))

(define-macro (match-map-tree-pre-order2 . sp)
  (let-alist*
   sp eq?
   ((loop-sym :filter car :default (gensym))
    (self-sym :filter car :default '*self*)
    (memtype  :filter car :key 'memorize)
    (target :filter car) (handler))
   ;; (format #t "mmt handlers : ~s\n" (hash-table-keys *components*))
   (let* ((handlers
	   (append-map1
	    (lambda (x)
	      (cond
	       ((pair? x) (list x))
	       ((hash-table-get *components* x #f)
		=> (lambda (x)
		     (limited-match-map-tree-pre-order
		      x
		      (('unquote 'loop) loop-sym)
		      (('unquote 'self) self-sym))))
	       (else
		(errorf "mmt handler ~s does not exists in ~s."
			x `(match-map-tree-pre-order2 ,sp)))))
	    handler))
	  (proc
	   `(lambda (,self-sym)
	      (match ,self-sym ,@handlers))))
     `(letrec ((,loop-sym
		,(if (not memtype)
		   proc
		   `(memorize ,memtype ,proc))))
	;; #?=',handlers
	(,loop-sym ,target)))))


;; (macro-debug
;;  (match-map-tree-pre-order2
;;   (target '(a b c d e))
;;   (handler mmt:default)))


(provide "maeve/lib/gauche/match-map-tree")
