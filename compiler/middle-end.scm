(define-module maeve.compiler.middle-end
  ;; Scheme -> MIR
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (use maeve.compiler.data-flow-analysis)
  (use maeve.compiler.misc)
  (export-all))

(select-module maeve.compiler.middle-end)

(define-macro (scheme->mir:match e tag . clauses)
  (let1 fuck-off-warning-of-match! (gensym)
    `(match
      ,e
      ,@(map
	 (match-lambda
	  (`((',sym . ,rest) ,body)
	   (let1 x (gensym)
	     `((',sym . ,x)
	       (match
		,x
		(,rest (=> ,fuck-off-warning-of-match!) ,body)
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
(define *default-module* (make-mod :name 'user))

(define (%module-core)
  (hash-table-get*
   *known-modules* 'core
   (error "module complex-type does not exist 0.")))

(define (compile-file file stop)
  (compile (file->sexp-list file) stop))

(define (%make-seq xs)
  (if (pair? xs)
    (if (length=1? xs) (car xs)
	(make-seq :es (seqflat xs)))
    (error "%make-seq : list required but got : " xs)))

(define (%normalize:trampoline %make-lvar x)
  (if (or (value-element? x) (lmd? x))
    (values x '())
    (let1 tmp (%make-lvar)
      (values tmp (list (make-set!-vls :dists (list tmp) :src x))))))

(define (%make-cpx-handler vls? loop-s %make-lvar %current-module tn spec)
  (decompose-def-cpx-type
   (hash-table-get*
    (mod:type-table-of %current-module) tn
    (begin
      (hash-table-for-each (mod:type-table-of %current-module) print)
      (error "Unkown complex type name :" tn))))
  (let* ((pres '()) (unfixed-size #f)
	 (%v (%make-lvar))
	 (inits
	  (kv-list-filter-map1
	   (lambda (k v)
	     (define (%n v)
	       (receive (v pre)
		   (%normalize:trampoline
		    %make-lvar (if (procedure? loop-s)
				 (loop-s v)
				 v))
		 (push! pres pre)
		 (values v pre)))
	     (case k
	       ((:unfixed-size)
		(receive (v pre) (%n v)
		  (set! unfixed-size v) #f))
	       (else
		(let1 sk (symbol-append k)
		  (cond
		   ((memq sk general-slots)
		    (receive (v pre) (%n v)
		      (make-set!-vls
		       :dists (list v)
		       :src
		       (make-mem
			:base
			(make-elm-addr
			 :base %v
			 :type-name tn :slot-name sk)))))
		   ((eq? sk unfixed-slot)
		    (make-seq
		     :es
		     (map1-with-index
		      (lambda (idx v)
			(receive (v pre) (%n v)
			  (make-set!-vls
			   :src v
			   :dists
			   (list (make-mem
				  :base
				  (make-elm-addr
				   :base %v
				   :type-name tn :slot-name sk
				   :index (make-scm-int idx)))))))
		      v)))
		   (else
		    (error "make-complex-type : unkown slot :" sk)))))))
	   spec)))
    (let1 cpx (make-allocate-cpx
	       :unfixed-size unfixed-size :type-name tn)
      (values
       (%make-seq
	`(,@(flat-1 pres)
	  ,(make-set!-vls
	    :dists (list %v)
	    :src cpx)
	  ,@inits
	  ,(if vls?
	     (make-vls :es (list %v))
	     %v)))
       cpx))))

(define (scheme->mir es stop)
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
  (define normalize:trampoline (cut %normalize:trampoline %make-lvar <>))
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
     ((eq? s '*variable-size*) (%make-asm-int (variable-size)))
     (else #f)))
  (define (fetch-variable s lvar . default)
    (cond
     ((assq-ref lvar s #f) => identity)
     ((fetch-gvar %current-module-table cunit s) => identity)
     (else
      (if (pair? default)
	(car default)
	(error "maeve-unbound : " s)))))
  (define (check-const e loop-s)
    (cond ((small-const-type? e) (%make-const e))
	  (((any-pred vector? string?) e) (loop-s `(quote ,e)))
	  (else #f)))
  (define *definitions* (make-hash-table 'eqv?))
  (define cunit (make-cunit :definitions *definitions*))
  (define *compile-time-module* (make-module #f))
  (copy&paste
   (define (scm:check-internal-macro e)
     (let loop ((e e))
       (scheme->mir:match
	e "scheme-syntax-error (internal macro)"
	(('let* (((? symbol? vs) es) ...) body . more)
	 (fold-right
	  (lambda (v e body) `(let ((,v ,e)) ,body))
	  (add-begin (cons body more))
	  vs es))
	(('let1 v e . b) `(let ((,v ,e)) ,@b))
	(cp:def
	 handler:set!
	 (('set! dist src) `(set!-values (,dist) ,src)))
	(((or 'define-macro 'define) (name . vs) . body)
	 (loop `(,(car e) ,name (lambda ,vs ,@body))))
	(((or 'define-macro) _ _)
	 (eval e *compile-time-module*)
	 '(begin))
	(e
	 (if (and (pair? e) (is-a? (eval `(guard (e (<error> #f))
						 ,(car e))
					 *compile-time-module*)
				   <macro>))
	   (let1 r (eval `(macroexpand ',e) *compile-time-module*)
	     (if (equal? e r) r (loop r)))
	   e)))))
   (define (il:check-internal-macro e)
     (let loop ((e e))
       (scheme->mir:match
	e "intermediate-language-syntax-error (internal macro)"
	(('inc! dist src) (loop `(set! ,dist (+ ,dist ,src))))
	(('dec! dist src) (loop `(set! ,dist (- ,dist ,src))))
	(cp:ref handler:set!)
	(else e))))
   (define (il-interface e lvar tail-ctx? in-lmd?)
     (let loop ((e e) (lvar lvar) (tail-ctx? tail-ctx?) (in-lmd? in-lmd?))
       (define (loop-s x) (loop x lvar tail-ctx? in-lmd?))
       (scheme->mir:match
	(il:check-internal-macro e) "intermediate-language-syntax-error"

	(('with-vars ((? symbol? vs) ...) . body)
	 (let1 lvar+ (map (cut %make-lvar <>) vs)
	   (%make-seq
	    (map (cut loop <> (append (map cons vs lvar+) lvar) tail-ctx? in-lmd?)
		 body))))

	;; S - ARITHMETIC OPERATION
	(('result i) (make-result :num i))
	(('register i) (make-register :num i))
	(((? (cut memq <> '(- + * / < > <= => =)) sym)
	  o1 o2)
	 (make-opr2 :opr sym :v1 (loop-s o1) :v2 (loop-s o2)))
	(((? (cut memq <> '(- !)) sym)
	  o1)
	 (make-opr1 :opr sym :v (loop-s o1)))
	;; E - ARITHMETIC OPERATION
	
	;; S - TYPE OPERATION
	(('define-immediate-types (? symbol? names) ...)
	 (for-each-with-index
	  (lambda (i x)
	    (unless (cunit:imm-type->tag-of cunit)
	      (set! (cunit:imm-type->tag-of cunit) (make-hash-table 'eq?)))
	    (hash-table-put! (cunit:imm-type->tag-of cunit) x i))
	  names)
	 (cunit:imm-type-tag-size-set!
	  cunit (integer-length (- (length names) 1)))
	 (make-seq))
	(('immediate-ref v . tag?)
	 (receive (v pre) (normalize:trampoline (loop-s v))
	   (%make-seq
	    `(,@pre ,(make-imm-ref :v v :tag-part? (get-optional tag? #f))))))
	(('make-immediate type v)
	 (receive (v pre) (normalize:trampoline (loop-s v))
	   (%make-seq `(,@pre ,(make-make-imm :type-name type :v v)))))

	(('define-complex-type (? symbol? name) (? integer? type-tag)
	   . slot-defs)
	 (let* ((uslots '())
		(gslots
		 (filter-map
		  (lambda (sd)
		    (if (pair? sd)
		      (and (not (and
				 (get-keyword :unfixed-size? (cdr sd) #f)
				 (begin (push! uslots (car sd)) #t)))
			   (car sd))
		      sd))
		  slot-defs)))
	   (unless (or (null? uslots) (length=1? uslots))
	     (error "too many unfixed size slot :" uslots))
	   (hash-table-put!
	    (mod:type-table-of %current-module) name
	    (make-def-cpx-type
	     :name name :type-tag type-tag :general-slots gslots
	     :unfixed-slot (if (null? uslots) #f (car uslots)))))
	 (make-seq))
	(('mem base . offset)
	 (make-mem :base (loop-s base)
		   :offset
		   (and-let* ((i (get-optional offset #f))
			      (_ (integer? i)))
		     i)))
	(('elm-addr base (? symbol? tn) (? symbol? sn) . idx)
	 (make-elm-addr
	  :type-name tn :slot-name sn
	  :base (loop-s base)
	  :index (cond
		  ((get-optional idx #f) => loop-s)
		  (else #f))))
	(('make-complex-object (? symbol? tn) . (? kv-list? spec))
	 (%make-cpx-handler #t loop-s %make-lvar %current-module tn spec))
	;; E - TYPE OPERATION

	(cp:def
	 handler:set-values!
	 (('set!-values dists src)
	  (make-set!-vls :dists (map loop-s dists) :src (loop-s src))))

	(('if test then els)
	 (%make-seq (make-if '() (loop-s test) (loop-s then) (loop-s els))))
	(('seq . es) (%make-seq (map loop-s es)))
	(('svar (and x (or 'sp 'fp))) (make-svar :type x))
	
	(('misc-const x) (%make-const x))
	(('call-c-function (? (any-pred string? symbol?) proc) . args)
	 (let1 x
	     (let1 proc #f
	       (cp:def
		call-process
		(receive (p/a pre)
		    (map2 (compose normalize:trampoline loop-s)
			  (cons proc args))
		  (%make-seq
		   `(,@(flat-1 pre)
		     ,(make-call :proc (car p/a) :args (cdr p/a)
				 :tail-ctx? tail-ctx?))))))
	   (call:slot-set!* x :proc (make-label :foregin? #t :name proc)
			    :abi (arch))))
	(cp:def
	 handler:gas-form
	 (('gas-form . form)
	  (make-foreign-code
	   :name (string-copy "gas")
	   :code `(,@(match-map-tree-pre-order2
		      (target form)
		      (handler
		       ((? symbol? i) (fetch-variable i lvar))
		       mmt:default))))))
	(cp:def
	 handler:quote
	 (('quote expr)
	  (rlet1 x (%make-const expr)
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
		    (list
		     (make-block
		      :es
		      (map
		       (cut loop <> (append (map cons vs lvar+) lvar) #t #t)
		       (cons body more)))))))
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
	  (if (null? es)
	    (make-seq :es '())
	    (receive (l o) (last+others es)
	      (%make-seq
	       `(,@(map loop-s o) ,(tail-loop-s l))))))
	 
	 (('if test then . els)
	  (let1 nels
	      (cond
	       ((get-optional els #f) => tail-loop-s)
	       (else
		(make-set!-vls :dists (list (make-result :num 0))
			       :src (%make-const 'undef))))
	    (receive (test-tmp pre) (normalize:trampoline (loop-s test))
	      (%make-seq
	       (make-if
		pre
		(make-opr2 :opr '= :v1 test-tmp :v2 (%make-const 'false))
		nels
		(tail-loop-s then))))))
	 ;; E - CONTROL
	 
	 ;; S - MODULE
	 (('define-module (? symbol? name) . exprs)
	  (let1 mod (make-mod :name name)
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
		 (hash-table-get*
		  *known-modules* name
		  (begin
		    (compile-file
		     (rlet1
		      r (find
			 (lambda (f)
			   (string=? (x->string name)
				     (values-ref (decompose-path f) 1)))
			 (*all-library-files*))
		      (unless r (error "import : Unknown module :" name)))
		     stop)
		    (hash-table-get *known-modules* name))))
	  (make-seq))

	 (('export (? symbol? syms) ...)
	  (update! (mod:exported-labels-of %current-module)
		   (pa$ lset-union eq? syms))
	  (make-seq))

	 ;; E - MODULE

	 (('il . es) (%make-seq (map (cut il-interface <> lvar tail-ctx? in-lmd?) es)))
	 
	 ;; S - CONST
	 (cp:ref handler:quote)
	 ;; E - CONST

	 ;; S - FUNCALL & REF VARIABLE
	 ((proc . args) (cp:ref call-process))
	 ((? symbol? sym) (fetch-variable sym lvar))
	 ;; E - FUNCALL & REF VARIABLE

	 (else
	  (cond
	   ((check-const e loop-s) => identity)
	   (else (error "scheme-syntax-error (else case) :" e)))))))))
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
   (extra-code:clause
    (define (process-set!-expr dist-of src-of)
      (define (normalize-dist self)
	(define pred0 value-element?)
	(define pred1 (any-pred block? seq?))
	(define (%update! dist proc)
	  (update!
	   (car
	    (last-pair
	     ((if (block? dist) block:es-of seq:es-of) dist)))
	   proc))
	(let loop ((self self))
	  (define (err)
	    (error "context-fault : dist of set!-vls or set! :" self))
	  (case/pred
	   self
	   (set!?
	    (let1 x (set!:dist-of self)
	      (cond
	       ((pred0 x) self)
	       ((pred1 x)
		(%update!
		 x (lambda (x)
		     (set! (set!:dist-of self) x)
		     (loop self)))
		x)
	       (else (err)))))
	   (set!-vls?
	    (let1 x (set!-vls:dists-of self)
	      (cond
	       ((every pred0 x) self)
	       ((find-and-others pred1 x)
		(lambda (_ x _) x)
		=> (lambda (pre dist post)
		     (%update!
		      dist
		      (lambda (x)
			(set! (set!-vls:dists-of self) `(,@pre ,x ,@post))
			(loop self)))
		     dist))
	       (else (err)))))
	   (else (error "Bad type (normalize-dist) :" self)))))
      (let loop0 ((self *self*))
	(define (src-set! x)
	  (set! (src-of self) x)
	  self)
	(let1 src (src-of self)
	  (case/pred
	   src
	   ((value-element? call? opr2? opr1? block-addr? allocate-cpx?
			    imm-ref? make-imm?)
	    (normalize-dist *self*))
	   (vls?
	    (let1 dist (dist-of self)
	      (if (pair? dist)
		(make-seq
		 :es
		 (map
		  loop-s
		  (%make-set!-sequence
		   (lambda (d s) (make-set!-vls :dists (list d) :src s))
		   (lambda () (make-lvar))
		   dist (vls:es-of src))))
		(make-seq
		 :es (list (loop-s src)
			   (src-set! (make-result :num 0)))))))
	   (with-mod?
	    (loop-s
	     (let loop1 ((s src))
	       (if (with-mod? s)
		 (with-mod:set-body! s (loop1 (with-mod:body-of s)))
		 (loop0 (src-set! s))))))
	   ((set!-vls? set!? foreign-code? sel-mod?)
	    (make-seq
	     :es (list (loop-s src) (src-set! (%make-const 'undef)))))
	   ((block? seq?)
	    (when-debug:normalize
	     (print "process-set!-expr block or seq case 1 :")
	     (il:pp/ss self))
	    (update! (car
		      (last-pair
		       ((if (block? src) block:es-of seq:es-of) src)))
		     (lambda (x)
		       (case/pred
			x
			((set!-vls? set!? foreign-code? sel-mod?)
			 (make-seq
			  :es
			  (list
			   x
			   (loop0
			    (src-set!
			     (let1 dist (dist-of self)
			       (if (pair? dist)
				 (make-vls
				  :es
				  (map-with-index1
				   (lambda (_ i) (make-result :num i))
				   dist))
				 (make-result :num 0))))))))
			(else
			 (loop0 (src-set! x))))))
	    (loop-s src))
	   (else (error "context-fault : src of set!-vls or set! :" *self*))))))
    (define (normalize2 accs)
      (define outer '())
      (define (trick accs)
	(let loop1 ((accs accs) (result #f))
	  (if (null? accs)
	    result
	    (let* ((acc (car accs)) (tgt (acc *self*)))
	      (case/pred
	       tgt
	       ((block? seq?)
		(let1 lp
		    (last-pair
		     ((if (block? tgt) block:es-of seq:es-of)
		      tgt))
		  (update!
		   (car lp)
		   (lambda (x) (set! (acc *self*) x) *self*))
		  (update! (car lp) loop-s)
		  (push!
		   outer
		   (lambda (extra)
		     (set! (car lp) extra)
		     tgt))
		  (loop1 (cdr accs) *self*)))
	       
	       (else
		(update! (acc *self*) loop-s)
		(loop1 (cdr accs) *self*)))))))
      (let1 r (trick accs)
	(fold (lambda (p e) (p e)) r outer))))
   (handler
    (opr2
     (normalize2 (list opr2:v1-of opr2:v2-of)))
    (call
     (normalize2 (list call:proc-of)))
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
	       (%make-const 'unbound)
	       e)))))
    (seq
     (*update!* :es (if in-lmd?
		      (normalize:block&others (map loop-s es))
		      (map loop-s es))))
    (set!     (*update!*)
	      (process-set!-expr set!:dist-of set!:src-of))
    (set!-vls (*update!*)
	      (process-set!-expr set!-vls:dists-of set!-vls:src-of))))
  (when-debug:flowgraph
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

(define (compile in stop)
  (let/cc escape
    (let* ((x (scheme->mir in stop))
	   (_ (when-stop "scheme->mir" x))
	   (omn
	    (cond
	     ((cunit:modules-of* x)
	      pair? =>
	      (lambda (xs)
		(symbol-join
		 (map mod:name-of xs)
		 "+")))
	     (else (symbol-append "noname" (eq-hash x)))))
	   (_ (when-debug:flowgraph (il->graphviz* #`",|omn|-1" x)))
	   (x (closure-convert x))
	   (_ (when-stop "closure-convert" x))
	   (x (normalize&reduce-graph omn x))
	   )
      (when-debug:flowgraph (il->graphviz* #`",|omn|-3" x))
      (when-stop "normalize-1" x)
      (with-output-to-mir-file
       omn (pretty-print x :use-global-table? #t))
      (debug:il:pp #`"compile ,omn extra" x)
      (make-compile-result
       :omn omn
       :imported-modules
       (flat-1
	(let* ((mods (cunit:modules-of* x))
	       (ims (map (compose (map$ mod:name-of*) mod:imported-modules-of*)
			 mods)))
	  ;; (format (current-error-port) "** import ~s : ~s\n" (map mod:name-of* mods) ims)
	  ims))))))

(define (closure-convert e)
  (let* ((extra-envs '())
	 (extra-toplevel '())
	 (parent-lmd-lvs '())
	 (closure->lbl (make-hash-table 'eq?))
	 (closure->reqvars (make-hash-table 'eq?))
	 (lbl->lmd (make-hash-table 'eq?))
	 (ne
	  (mir-traverse
	   (target e)
	   (use-circular-graph?)
	   (inherited-attr (envs '() *inherit*))
	   (handler
	    (lmd
	     (define (%make-lvar)
	       (rlet1 lv (make-lvar)
		      (push! (cadr parent-lmd-lvs) lv)))
	     (push! extra-envs (list #f))
	     (push! parent-lmd-lvs local-vars)
	     (let* ((es (map
			 (*cut-loop* :self <> :envs (cons param envs))
			 es))
		    (reqvars (remove
			      (lambda (e) (memq e param))
			      (drop-right (pop! extra-envs) 1))))
	       (define (%update) (*update!* :es es :extra-env reqvars
					    :local-vars (pop! parent-lmd-lvs)))
	       (for-each (lambda (e) (push! (car extra-envs) e)) reqvars)
	       (if (parent-is-a-deflabel?)
		 (%update)
		 (let*-values
		     (((lbl) (make-label :module %current-module))
		      ((clo %allocate-cpx)
		       (%make-cpx-handler
			#f #f %make-lvar
			(%module-core)
			'closure
			(list :lbl lbl :elms reqvars
			      :unfixed-size (make-scm-int (length reqvars))
			      :length (make-scm-int (length reqvars))))))
		   (hash-table-put! closure->lbl %allocate-cpx lbl)
		   (hash-table-put! closure->reqvars %allocate-cpx reqvars)
		   (push! extra-toplevel
			  (let1 x (make-deflabel :e (%update) :lbl lbl)
			    (hash-table-put! lbl->lmd lbl *self*)
			    (if %current-module
			      (make-with-mod
			       :module %current-module :body x)
			      x)))
		   clo))))
	    (lvar
	     (and-let* ((env (find (lambda (e) (member *self* e il:eqv?)) envs)))
	       (update! (car extra-envs) (cut lset-adjoin eq? <> *self*)))
	     (*update!*))))))
    (update! (cunit:es-of* ne) (cut append (reverse! extra-toplevel) <>))
    (update! ne (cut normalize&reduce-graph #f <>))
    (hash-table-for-each
     (reach ne)
     (lambda (stm rd)
       (when (call? stm)
       (format #t " * ~s\n" (il->sexp/ss stm))
       (hash-table-for-each
	rd (lambda (v es)
	     (for-each
	      (lambda (e)
		(decompose-rd-elm e)
		(format #t "  ~s = ~s\n" (il->sexp/ss dist)
			(il->sexp/ss src)))
	      es))))))
    (let1 %reach (reach ne)
(macro-debug
      (mir-traverse
       (use-debug:print-self?)
       (use-circular-graph?)
       (target ne)
       (handler
	(call
	 #?=(if (not (lvar? proc))
	   (*update!*)
	   (let1 prd (hash-table-get (hash-table-get %reach *self*) proc)
	     (unless (length=1? prd)
	       (error "closure-convert : a lot of RD :" prd))
	     (let-decompose-rd-elm
	      (car prd)
	      (if (not (and (allocate-cpx? src)
			    (eq? 'closure (allocate-cpx:type-name-of src))))
		(*update!*)
		(make-seq
		 :es
		 `(,@(map
		      (lambda (d s) (make-set!-vls :src s :dists (list d)))
		      (lmd:extra-env-of
		       (hash-table-get lbl->lmd (hash-table-get closure->lbl src)))
		      (hash-table-get closure->reqvars src))
		   ,(*update!*
		     :proc (make-elm-addr
			    :base proc
			    :type-name 'closure :slot-name 'lbl)))))))))))))))

;; (define (closure-convert e)
;;   (define (mark e)
;;     (let1 extra-vars '()
;;       (mir-traverse
;;        (target e)
;;        (use-circular-graph?)
;;        (inherited-attr (envs '() *inherit*))
;;        (handler
;; 	(lmd
;; 	 (push! extra-vars (list #f))
;; 	 (let ((nes (map (cut loop <> (cons args envs)) es))
;; 	       (reqvars (reverse
;; 			 (remove
;; 			     (lambda (e) (memq e args))
;; 			     (drop-right (pop! extra-vars) 1)))))
;; 	   (for-each (lambda (e) (push! (car extra-vars) e)) reqvars)
;; 	   (*update!*
;; 	    :env reqvars :es nes)))
;; 	(lvar
;; 	 (let1 env
;; 	     (or
;; 	      (find (lambda (e) (memq *self* e)) envs)
;; 	      (error "closure-convert 0 :" *self*))
;; 	   (unless (eq? env (car envs))
;; 	     (update! (car extra-vars) (cut lset-adjoin/save-order eq? <> s)))
;; 	   (*update!*)))))))
;;   (define (move-toplevel e)
;;     (let* ((lmds '())
;; 	   (e
;; 	    (mir-traverse
;; 	     (target e)
;; 	     (handler
;; 	      (lmd
;; 	       (if (parent-is-a-define?)
;; 		 (*update!*)
;; 		 (push! lmds
;; 			(make-
;; 	     (let loop ((e e))
;; 		(match
;; 		 e
;; 		 (('lambda args es ...)
;; 		  (let1 name (gensym)
;; 		    (push! lmds `(define ,name (lambda ,args ,@(map loop es))))
;; 		    `(closure ,name ,(car args))))
;; 		 (('lvar _ _) e)
;; 		 ((xs ...) (map loop xs))
;; 		 (else e)))))
;;       `(,@(reverse! lmds) ,e)))
;;   (move-toplevel (mark e)))
       

(provide "maeve/compiler/middle-end")
