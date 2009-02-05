(define-module maeve.lib.gauche.macro-util
  (use srfi-1)
  (use srfi-42)
  (use util.match)
  (use maeve.lib.gauche.pp)
  (use maeve.lib.gauche.values)
  (use maeve.lib.gauche.complex-iterator)
  (export-all))

(select-module maeve.lib.gauche.macro-util)

(define-macro (case/pred obj . clauses)
  (let1 x (gensym)
    `(let ((,x ,obj))
       (cond
	,@(map
	   (lambda (c)
	     (let loop ((c c))
	       (match
		c
		((pred0 pred1 '=> proc)
		 `(,(car (loop (list pred0))) ,pred1 => ,proc))
		((pred0 '=> proc)
		 `(,(car (loop (list pred0))) => ,proc))
		((('and preds ...) body ...)
		 `((and ,@(map (cut list <> x) preds)) ,@body))
		((('debug-print x) xs ...)
		 (let1 x (loop (cons x xs))
		   `((debug-print ,(car x)) ,@(cdr x))))
		(((preds ...) body ...)
		 `((or ,@(map (cut list <> x) preds)) ,@body))
		(('else body ...) c)
		((pred body ...) `((,pred ,x) ,@body))
		(else
		 (error "malformed case/pred" `(case/pred ,obj ,@clauses))))))
	   clauses)))))

(define-macro (mac x) (eval x (current-module)))

(define-macro (mcut mac . forms)
  (receive (vs nforms)
      (filter-map2
       (lambda (x)
	 (if (eq? x '<>)
	   (let1 g (gensym)
	     (values g g))
	   (values #f x)))
       (cons mac forms))
    `(lambda ,vs ,nforms)))

(define-macro (insert-code x y) `(if ,x ,y '()))
(define-macro (insert-code* x y) `(if ,x (list ,y) '()))
(define-macro (cond1-nil test proc)
  `(cond
    (,test => ,proc)
    (else '())))

(define-macro (nand . exprs) `(not (and ,@exprs)))
(define-macro (nor  . exprs) `(not (or  ,@exprs)))

(define (any* proc . xs) (any proc xs))
(define (every* proc . xs) (every proc xs))

(define (%last+others xs)
  (let loop ((xs xs) (rs '()))
    (if (null? (cdr xs))
      (values (car xs) (reverse! rs))
      (loop (cdr xs) (cons (car xs) rs)))))

(define-macro (any-pred* . xs)
  (receive (arg preds) (%last+others xs)
    `(or ,@(map (cut list <> arg) preds))))

(define-macro (every-pred* . xs)
  (receive (arg preds) (%last+others xs)
    `(and ,@(map (cut list <> arg) preds))))

(define-macro (with-variables* vars init-v . body)
  `(let ,(map (cut list <> init-v) vars)
     ,@body))

(define-macro (with-gensyms vars . body)
  `(with-variables* ,vars (gensym) ,@body))

(define-macro (filter-let vars filter . body)
  `(let ,(map (lambda (v) `(,v (,filter ,v))) vars)
     ,@body))

(define-macro (define-sub-operator ops . specs)
  `(begin
     ,@(append-map1
	(lambda (spec)
	  (match-let1
	   (lambda-list name-trans body-trans) spec
	   (filter-let
	    (name-trans body-trans)
	    (cut eval <> (current-module))  
	    (map
	     (lambda (op)
	       `(define (,(name-trans op) ,@lambda-list)
		  ,(body-trans op)))
	     ops))))
	specs)))

(define-macro (rletrec1 name x . body) `(letrec ((,name ,x)) ,@body ,name))
(define-macro (rlet*-car vspec . body)
  `(let* ,vspec ,@body ,(car (map car vspec))))
(define-macro (rlet*-last vspec . body)
  `(let* ,vspec ,@body ,(last (map car vspec))))
(define-macro (rlet* vspec . body)
  `(let* ,vspec ,@body (values ,@(map car vspec))))
(define-macro (rlet*-reverse vspec . body)
  `(let* ,vspec ,@body (values ,@(reverse! (map car vspec)))))
(define-macro (rlet*-list vspec . body)
  `(let* ,vspec ,@body (list ,@(map car vspec))))
(define-macro (rlet*-list+reverse vspec . body)
  `(let* ,vspec ,@body (list ,@(reverse! (map car vspec)))))
(define-macro (rlet1    name x . body) `(let    ((,name ,x)) ,@body ,name))
(define-macro (rlet1-values name x . body)
  `(receive ,name ,x ,@body (apply values ,name)))
(define-macro (r2let1    name x . body)
  `(let ((,name ,x)) ,@body
	(values ,name ,name)))

(define (symbol-append . rest)
  (string->symbol (string-join (map x->string rest) "")))

(define (gensyms spec)
  (cond
   ((list? spec)
    (map (lambda _ (gensym)) spec))
   ((number? spec)
    (list-ec (: i 0 spec) (gensym)))
   (else
    (error "gensyms : Unsupported type :" spec))))

(define-macro (with-accumlator acs . body)
  (let1 r (gensym)
    `(let* (,@acs
	    (,r (begin ,@body)))
       (values
	,r
	,@acs))))

(define (macroexpand-all form)
  (let loop ((form form))
    (format/ss "~s" form)
    (if (pair? form)
      (let1 r (macroexpand form)
	(if (pair? r)
	  (if (equal? r form)
	    (map loop r)
	    (loop r))
	  r))
      form)))

(define-macro (macro-debug-all form)
  (let1 form (macroexpand-all form)
    (pretty-print form)
    form))

(define-macro (macro-debug form)
  (let1 form (macroexpand form)
    (pretty-print form)
    form))

(define-macro (macro-debug-1 form)
  (let1 form (macroexpand-1 form)
    (pretty-print form)
    form))

(provide "maeve/lib.gauche/macro-util")
