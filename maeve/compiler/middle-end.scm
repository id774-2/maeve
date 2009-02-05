(define-module maeve.compiler.middle-end
  ;; Scheme -> MIR
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (export-all))

(select-module maeve.compiler.middle-end)

(define-macro (scheme->mir:match e tag . clauses)
  (let1 fuck-warning-of-match! (gensym)
    `(match
      ,e
      ,@(map
	 (match-lambda
	  (`((',sym . ,rest) ,body)
	   (let1 x (gensym)
	     `((',sym . ,x)
	       (match
		,x
		(,rest (=> ,fuck-warning-of-match!) ,body)
		(else (errorf "maeve : ~a : ~s" ',tag e))))))
	  (x x))
	 clauses))))

(define-macro copy&paste
  (let1 *copy&paste-table* (make-hash-table 'eq?)
    (lambda es
      `(begin
	 ,@(match-map-tree-pre-order2
	    (target es)
	    (handler
	     (('cp:ref x)
	      (hash-table-get*
	       *copy&paste-table* x
	       (errorf "copy&paste : (cp:ref ~s) does not exists."
		       x)))
	     (('cp:def n e) (hash-table-put! *copy&paste-table* n e) e)
	     mmt:default))))))

(define *known-modules* (make-hash-table 'eq?))
(define *default-module* (make-mod :name 'user :table (make-hash-table 'eq?)))

(define (%make-seq xs)
  (if (pair? xs)
    (if (length=1? xs) (car xs)
	(make-seq :es (seqflat xs)))
    (error "%make-seq : list required but got : " xs)))

(define (scheme->mir es)
  (define (add-begin x)
    (if (pair? x)
      (if (length=1? x)
	(car x)
	`(begin ,@x))
      x))
  (define %current-module *default-module*)
  (define %current-module-table (mod:table-of *default-module*))
  (define %local-vars '())
  (define (%make-lvar . opt-name)
    (when (null? %local-vars) (error "%local-vars is null."))
    (rlet1 lv (make-lvar :name (get-optional opt-name #f))
	   (push! (car %local-vars) lv)))
  (define (make-if pres test then els)
    (let* ((end-block (make-block))
	   (then-block
	    (make-block
	     :es (seqflat (list then))
	     :default-succ (%make-block-addr end-block)))
	   (els-block
	    (make-block
	     :es (seqflat (list els))
	     :default-succ (%make-block-addr end-block)))
	   (pre-block
	    (make-block
	     :es pres :test test
	     :default-succ (%make-block-addr els-block)
	     :opt-succ (%make-block-addr then-block))))
      (list pre-block then-block els-block end-block)))
  (define (normalize:trampoline x)
    (if (value-element? x)
      (values x '())
      (let1 tmp (%make-lvar)
	(values tmp (list (make-set!-vls :dists (list tmp) :src x))))))
  (define (fetch-gvar %current-module-table cunit s)
    (define %make (mcut make-mem :base <>))
    (cond
     ((hash-table-get %current-module-table s #f) => %make)
     ((find-and-value
       (lambda (m)
	 (find-and-value
	  (lambda (m)
	    (and
	     (memq s (mod:exported-labels-of m))
	     (hash-table-get (mod:table-of m) s #f)))
	  (mod:imported-modules-of m)))
       (cunit:modules-of cunit))
      => (lambda (lbl)
	   (update!
	    (mod:imported-labels-of %current-module)
	    (cut lset-adjoin il:eqv? <> lbl))
	   (%make lbl)))
     ((eq? s '*variable-size*) (make-const :v (variable-size)))
     (else #f)))
  (define (fetch-variable s lvar . default)
    (cond
     ((assq-ref lvar s #f) => identity)
     ((fetch-gvar %current-module-table cunit s) => identity)
     (else
      (if (pair? default)
	(car default)
	(error "maeve-unbound : "s)))))
  (define (check-const e loop-s)
    (cond ((small-const-type? e) (make-const :v e))
	  (((any-pred vector? string?) e) (loop-s `(quote ,e)))
	  (else #f)))
  (define *definitions* (make-hash-table 'eqv?))
  (define cunit (make-cunit :definitions *definitions*))
  (copy&paste
   (define (scm:check-internal-macro e)
     (scheme->mir:match
      e
      "scheme-syntax-error (internal macro)"
      (('let* (((? symbol? vs) es) ...) body . more)
       (fold-right
	(lambda (v e body) `(let ((,v ,e)) ,body))
	(add-begin (cons body more))
	vs es))
      (('let1 v e b) `(let ((,v ,e)) ,body))
      (cp:def
       handler:set!
       (('set! dist src) `(set!-values (,dist) ,src)))
      (else
       (match
	e
	(('define (name . vs) . body)
	 `(define ,name (lambda ,vs ,@body)))
	(e e)))))
   (define (il:check-internal-macro e)
     (let loop ((e e))
       (scheme->mir:match
	e "intermediate-language-syntax-error (internal macro)"
	(('inc! dist src) (loop `(set! ,dist (+ ,dist ,src))))
	(('dec! dist src) (loop `(set! ,dist (- ,dist ,src))))
	(cp:ref handler:set!)
	(else e))))
   (define (il-interface expr lvar in-lmd?)
     (let loop ((e expr) (lvar lvar) (in-lmd? in-lmd?))
       (define loop-s (cut loop <> lvar in-lmd?))
       (scheme->mir:match
	(il:check-internal-macro e) "intermediate-language-syntax-error"
	;; S - ARITHMETIC OPERATION

	(('with-vars ((? symbol? vs) ...) . body)
	 (let1 lvar+ (map (cut %make-lvar <>) vs)
	   (%make-seq
	    (map (cut loop <> (append (map cons vs lvar+) lvar) in-lmd?)
		 body))))
	(('result i) (make-result :num i))
	(('register i) (make-register :num i))
	(((? (cut memq <> '(- + * / < > <= => =)) sym)
	  o1 o2)
	 (make-opr2 :opr sym :v1 (loop-s o1) :v2 (loop-s o2)))
	(((? (cut memq <> '(- !)) sym)
	  o1)
	 (make-opr1 :opr sym :v (loop-s o1)))
	;; E - ARITHMETIC OPERATION
	
	(cp:def
	 handler:set-values!
	 (('set!-values dists src)
	  (make-set!-vls :dists (map loop-s dists) :src (loop-s src))))

	(('if test then els)
	 (%make-seq (make-if '() (loop-s test) (loop-s then) (loop-s els))))
	(('seq . es) (%make-seq (map loop-s es)))
	(('svar (and x (or 'sp 'fp))) (make-svar :type x))
	(('mem base (? integer? offset))
	 (make-mem :base (loop-s base) :offset offset))

	(('misc-immidate x) (make-misc-const x))
	(('call-c-function (? symbol? func) . args)
	 ;; using parameterized-arch
	 (loop-s ((make-call-c-function) func args)))

	(cp:def
	 handler:gas-form
	 (('gas-form . form)
	  (make-foreign-code
	   :name "gas"
	   :code `(,@(match-map-tree-pre-order2
		      (target form)
		      (handler
		       ((? symbol? i) (fetch-variable i lvar))
		       mmt:default))))))
	(cp:def
	 handler:quote
	 (('quote expr)
	  (rlet1 x (make-const :v expr)
		 (when (large-const-type? expr)
		   (push! (cunit:large-consts-of cunit) x)))))
	((? symbol? s) (fetch-variable s lvar))
	(else
	 (cond
	  ((check-const e loop-s) => identity)
	  (else
	   (error "intermediate-language-syntax-error (else case) :" e)))))))
   (define (trans e)
     (let loop ((e e) (lvar '()) (tail-ctx? #t) (in-lmd? #f))
       (define loop-s (cut loop <> lvar #f in-lmd?))
       (define tail-loop-s (cut loop <> lvar tail-ctx? in-lmd?))
       ((lambda (r)
	  (if (and tail-ctx? (value-element? r))
	    (make-set!-vls :src r :dists (list (make-result :num 0)))
	    r))
	(scheme->mir:match
	 (scm:check-internal-macro e)
	 "scheme-syntax-error"

	 (cp:ref handler:gas-form)
	 (cp:ref handler:set-values!)
	 (('values . es)
	  (receive (es pres)
	      (map2 (compose normalize:trampoline loop-s) es)
	    (%make-seq
	     `(,@(flat-1 pres) ,(make-vls :es es)))))

	 ;; S - PROCEDURE
	 (('lambda vs body . more)
	  (push! %local-vars '())
	  (let* ((rest-arg? (dotted-list? vs))
		 (lvar+
		  (map (mcut make-lvar :name <>)
		       (if rest-arg?
			 (dotted-list->proper-list vs)
			 vs)))
		 (body
		  (let1 body-var (append (map cons vs lvar+) lvar)
		    (map
		     (cut loop <> (append (map cons vs lvar+) lvar) #t #t)
		     (cons body more)))))
	    (make-lmd :param lvar+ :local-vars (pop! %local-vars)
		      :rest-arg? rest-arg? :es body)))

	 (((and (or 'let 'letrec) s) (((? symbol? vs) es) ...) body . more)
	  (let* ((lvar+ (map (cut %make-lvar <>) vs))
		 (body-lvar (append (map cons vs lvar+) lvar))
		 (e-lvar    (if (eq? 'let s) lvar body-lvar)))
	    (%make-seq
	     `(,(make-set!-vls
		 :dists lvar+
		 :src (make-vls :es (map (cut loop <> e-lvar #f in-lmd?) es)))
	       ,(loop (add-begin (cons body more))
		      body-lvar tail-ctx? in-lmd?)))))
	 ;; E - PROCEDURE

	 ;; S - CONTROL
	 (('define name v)
	  (let1 lbl (make-label :name name :module %current-module)
	    (when (eq? name 'main)
	      (cunit:entry-point-set! cunit lbl))
	    (hash-table-put! %current-module-table name lbl)
	    (%make-deflabel lbl (loop-s v))))

	 (('begin . es)
	  (receive (l o) (last+others es)
	    (%make-seq
	     `(,@(map loop-s o) ,(tail-loop-s l)))))

	 (('if test then . els)
	  (let1 nels
	      (cond
	       ((get-optional els #f) => tail-loop-s)
	       (else
		(make-set!-lvs :dists (list (make-result :num 0))
			       :src (make-misc-const 'undef))))
	    (receive (test-tmp pre) (normalize:trampoline (loop-s test))
	      (%make-seq
	       (make-if
		pre
		(make-opr2 :opr '= :v1 test-tmp :v2 (make-misc-const 'false))
		nels
		(tail-loop-s then))))))
	 ;; E - CONTROL
	 
	 ;; S - MODULE
	 (('define-module (? symbol? name) . exprs)
	  (let1 mod (make-mod :name name :table (make-hash-table 'eq?))
	    (push! (cunit:modules-of cunit) mod)
	    (hash-table-put! *known-modules* name mod)
	    (if (null? exprs)
	      (make-seq)
	      (let1 e (with-mod-for-handler mod (tail-loop-s (add-begin exprs)))
		(make-with-mod :module mod :body e)))))

	 (('select-module (? symbol? name))
	  (let1 mod
	      (hash-table-get*
	       *known-modules* name
	       (error "select-module : Unknown module" name))
	    (sel-mod-for-handler mod)
	    (make-sel-mod :module mod)))
	 
	 (('require (? symbol? name))
	  (let1 name (if (#/\.scm$/ name) (string-append name ".scm") name)
	    (compile-module
	     (cond
	      ((find-and-value
		(lambda (b)
		  (call-with-input-file (build-path b name)
		    read :if-does-not-exist #f))
		*load-path*) => identity)
	      (else
	       (errorf "cannot find file ~s in *load-path*" name)))))
	  (make-seq))

	 (('import (? symbol? name))
	  (push! (mod:imported-modules-of %current-module)
		 (hash-table-get* *known-modules* name
				  (error "import : Unknown module :" name)))
	  (make-seq))

	 (('export (? symbol? syms) ...)
	  (update! (mod:exported-labels-of %current-module)
		   (pa$ lset-union eq? syms))
	  (make-seq))

	 ;; E - MODULE

	 (('il expr) (il-interface expr lvar in-lmd?))
	 
	 ;; S - CONST
	 (cp:ref handler:quote)

	 ;; S - FUNCALL & REF VARIABLE
	 ((proc . args)
	  (receive (p/a pre)
	      (map2 (compose normalize:trampoline loop-s)
		    (cons proc args))
	    (%make-seq
	     `(,@(flat-1 pre)
	       ,(make-call :proc (car p/a) :args (cdr p/a)
			   :tail-ctx? tail-ctx?)))))
	 ((? symbol? sym) (fetch-variable sym lvar))
	 ;; E - FUNCALL & REF VARIABLE

	 (else
	  (cond
	   ((check-const e loop-s) => identity)
	   (else (error "scheme-syntax-error (else case) :" e)))))
	;; E - CONST
	))))
  (cunit:es-set! cunit (map trans es)))


(define (compute-unijump-sequence jump-table)
  (let ((rjump-table #0=(make-hash-table (hash-table-type jump-table)))
	(del-table #0#))
    (hash-table-for-each
     jump-table
     (lambda (preds succs)
       (for-each (cut hash-table-push! rjump-table <> preds) succs)))
    (filter
     (compose not undefined?)
     (hash-table-map
      rjump-table
      (lambda (succ preds)
	(define (loop main-table check-table xs)
	  (unfold
	   (lambda (xs)
	     (not
	      (and (length=1? xs)
		   (length=1? (hash-table-get check-table (car xs))))))
	   car
	   (lambda (xs) (hash-table-get main-table (car xs) '()))
	   xs))
	(unless (hash-table-exists? del-table succ)
	  (let* ((x (reverse! (loop rjump-table jump-table preds)))
		 (y (loop jump-table rjump-table (list succ))))
	    (let1 r (append x y)
	      (for-each
	       (lambda (x) (hash-table-put! del-table x #t))
	       r)
	      (when (length>2? r) r)))))))))

;; (compute-unijump-sequence
;;  (alist->hash-table
;;   '((a b) (b 0) (x y) (y 0) (0 1) (1 2) (2 3))
;;   'eqv?))
;; ;; => ((0 1) (x y) (a b))

(define (normalize&reduce-graph require-graphviz? e)
  (define lbl->block (make-hash-table 'eqv?))
  (define lbl-ref (make-hash-table 'eqv?))
  (define lbl->parent-proc (make-hash-table 'eqv?))
  (define pred->succ-1 (make-hash-table 'eqv?))
  (define initialize-cunit '())
  (define %result #f)
  (mir-traverse
   (target e)
   (use-circular-graph?)
   (inherited-attr (in-lmd? #f *inherit*))
   (extra-code:loop
    (define (record-block b)
      (define (p1! x)
	(when x
	  (hash-table-update! lbl-ref x (cut lset-adjoin eqv? <> id) '())))
      (decompose-block b)
      (p1! default-succ) (p1! opt-succ)
      (cond
       ((and default-succ (not opt-succ)
	     (block-addr:name-of* default-succ))
	integer? =>
	(lambda (tgt) (hash-table-put! pred->succ-1 id (list tgt)))))
      (hash-table-put! lbl->block id b)
      (hash-table-put!
       lbl->parent-proc id
       (cond
	((find lmd? (cons *self* *parent-nodes*)) => identity)
	(else (error "lmd element does not exists in parent nodes :"
		     id  (map il->sexp/ss *parent-nodes*))))))
    (define (normalize:block&others es . opt-orig-block)
      (define (%block x)
	(case/pred
	 x ((null? pair?) (make-block :es x)) (block? x)
	 (else (error "filter-block :" x))))
      (receive (rest others)
	  (cond
	   ((let loop ((xs (seqflat-all es)) (result '()))
	      (receive (pre block rest) (find-and-others block? xs)
		(if (null? rest)
		  #0=(filter*-list* block pre result)
		  (loop rest #0#))))
	    pair? => car+cdr)
	   (else (values '() '())))
	(rlet1
	 blocks
	 (fold
	  (lambda (x blocks)
	    (let1 block (%block x)
	      (unless (block-has-no-test-jump? block)
		(%block:default-succ-set! block (car blocks)))
	      (cons block blocks)))
	  (list
	   (block:succs-copy!
	    (%block rest)
	    (get-optional opt-orig-block '())))
	  others)
	 (for-each record-block blocks)))))
   (handler
    (block
     (let1 fes (map loop-s (seqflat-all es))
       (begin0
	 (cond
	  ((cut find block? fes)
	   (let1 blocks (normalize:block&others fes *self*)
	     (%make-seq
	      (cons (*update!*
		     :default-succ (%make-block-addr (car blocks))
		     :es '() :test #f :opt-succ #f)
		    blocks))))
	  (else (*update!* :es fes)))
	 (record-block *self*))))
    (lmd
     (*update!*
      :es (normalize:block&others (map (*cut-loop* :self <> :in-lmd? #t) es))))
    (cunit
     (begin0
       (*update!*)
       (unless (null? initialize-cunit)
	 (cond
	  ((and init-point
		(hash-table-get definitions init-point #f))
	   => (lambda (df)
		(update!
		 (block:es-of (car (lmd:es-of (deflabel:e-of df))))
		 (pa$ cons initialize-cunit))))
	  (else
	   (let1 init (make-label :name (symbol-append 'init id))
	     (cunit:init-point-set! *self* init)
	     (update!
	      (cunit:es-of *self*)
	      (pa$ cons
		   (loop-s
		    (%make-deflabel
		     init
		     (make-lmd
		      :es (list (make-block :es initialize-cunit)))))))))))))
    (deflabel
      (let* ((data-definition? (not (lmd? e)))
	     (reqinit? (and data-definition?
			    (not (label? e)) (not (const? e)))))
	(when reqinit?
	  (push! initialize-cunit
		 (make-set!-vls :dists (list (make-mem :base lbl))
				:src (loop-s e))))
	(*update!*
	 :e (loop-s
	     (if reqinit? 
	       (make-const :v ((make-misc-immidiate) 'unbound))
	       e)))))
    (seq
     (*update!* :es (if in-lmd?
		      (normalize:block&others (map loop-s es))
		      (map loop-s es))))
    (set!-vls
     (define expr/val? (any-pred value-element? call? vls? opr2? opr1?))
     (case/pred
      src
      (expr/val? (*update!*))
      (with-mod?
       (loop-s
	(let loop ((s src))
	  (if (with-mod? s)
	    (with-mod:set-body! (loop s))
	    (set!-vls:set-src! *self* s)))))
      (((any-pred set!-vls? foreign-code? sel-mod?))
       (make-seq
	:es (list (loop-s src) (*update!* :src (make-misc-const 'undef)))))
      ((block? seq?)
       ((if (block? src)
	  block:es-append-post!
	  (lambda (x y) (update! (seq:es-of x) (cut append <> y))))
	src
	(list
	 (*update!*
	  :src (make-vls
		:es (map1-with-index
		     (lambda (i _) (make-result :num i))
		     dists)))))
       (loop-s src))
      (else (error "context-fault : set!-vls src :" src))))))
  (when-debug
   (when require-graphviz?
     (il->graphviz* #`",|require-graphviz?|-2" e)))
  (let1 get-block (pa$ hash-table-get lbl->block)
    (for-each
     (lambda (xs)
       (define target (get-block (car xs)))
       (define lmd (hash-table-get lbl->parent-proc (car xs)))
       (update!
	(block:es-of target)
	(lambda (es)
	  (apply
	   append es
	   (map (lambda (l)
		  (cond
		   ((get-block l #f)
		    => (lambda (b) (lmd:block-delete! lmd b) (block:es-of b)))
		   (else '())))
		(cdr xs)))))
       (block:succs-copy! target (get-block (last xs))))
     (compute-unijump-sequence pred->succ-1)))
  e)

(provide "maeve/compiler/middle-end")