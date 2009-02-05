(define-module maeve.compiler.intermediate-language-util
  (extend srfi-1 srfi-13 srfi-42 srfi-43
	  util.list file.util util.match gauche.parameter text.tree
	  gauche.process
	  maeve.lib.gauche.pp
	  maeve.lib.gauche.misc
	  maeve.lib.gauche.graph
	  maeve.lib.gauche.debug
	  maeve.lib.gauche.values
	  maeve.lib.gauche.list-util
	  maeve.lib.gauche.macro-util
	  maeve.lib.gauche.match-map-tree
	  maeve.lib.gauche.complex-iterator
	  maeve.compiler.arch
	  maeve.compiler.file-definitions)
  (export-all))

(select-module maeve.compiler.intermediate-language-util)

(debug-print-width 10000000)

(define (identity a) a)

(define (check-and-eval-car ys)
  (eval (car (check-eval-spec ys))
	(current-module)))

(define (map-check-and-eval xs)
  (map
   (cut eval <> (current-module))
   (check-eval-spec xs)))

(define (check-eval-spec xs)
  (fold-right
   (lambda (x p)
     (match
      x
      (('eval . es) (cons #0=(eval `(begin ,@es) (current-module)) p))
      (('eval-list . es) (append #0# p))
      (else (cons x p))))
   '()
   xs))

(define il:copy vector-copy)

(define il:class (cut vector-ref <> 0))

(define il:id
  (getter-with-setter
   (cut vector-ref <> 1)
   (lambda (v x) (vector-set! v 1 x))))

(define (il:eqv? a b)
  (and
   (vector? a) (vector? b)
   (eq? (il:class a) (il:class b))
   (eqv? (il:id a) (il:id b))))

(define (il<? a b)
  (and
   (vector? a) (vector? b)
   (< (il:id a) (il:id b))))

(define *traverse-default-handlers* (make-hash-table 'equal?))

(define (il:slot-name->getter name slot-name)
  (symbol-append name ":" slot-name "-of"))

(define (il:slot-name->setter name slot-name)
  (symbol-append name ":" slot-name "-set!"))

(define (il:slot-name->interhandler-ref-var slot-name)
  (symbol-append "*" slot-name "*"))

(define (il:struct-name->multiple-slot-setter name)
  (symbol-append name ":slot-set!*"))

(define (il:struct-name->struct-specs name)
  (symbol-append name "-struct-specs"))

(define (error:unknown-il-element . rest)
  (apply error "Unknown ast struct element :" rest))

(define (slot-name->sdf-table-ref name)
  (symbol-append "*" name "-ref*"))

(define *sdf-table-ref-syms* '())

(define il-struct-specs (make-hash-table 'eq?))

(define (il? x)
  (and (vector? x) (> (vector-length x) 0)
       (hash-table-exists? il-struct-specs (il:class x))))

(define (il:set-new-id! x)
  (when (il? x) (vector-set! x 1 (struct-id-gen)))
  x)

(define struct-id-gen (let1 c -1 (lambda () (inc! c))))

(define il-spec-slot-name (cut vector-ref <> 0))
(define il-spec-slot-section (cut vector-ref <> 1))
(define il-spec-slot-type (cut vector-ref <> 2))
(define il-spec-slot-struct (cut vector-ref <> 3))
(define il-spec-slot-interhandler-ref? (cut vector-ref <> 4))
(define il-spec-slot-special-slot-handler (cut vector-ref <> 5))
(define il-spec-slot-init-value (cut vector-ref <> 6))
(define il-spec-slot-allow-print? (cut vector-ref <> 7))
(define il-spec-slot-misc (cut vector-ref <> 8))

(define-macro (with-decompose-il-slot-spec sd . body)
  `(match-let1
    #(sname section type sstruct interhandler-ref? sp-shandler init-value allow-print? misc) ,sd
    ,@body))

(define %traverse-macro-name  '())
(define %extra-inherited-attr '())

(define-mmt-handlers
  ifu:safety
  (((? (cut memq <> %traverse-macro-name) x) . xs) (cons x xs)))

(define (parse-cut-macro-spec xs expr-trans)
  (let1 rest-arg '()
    (receive (args expr)
	(map2
	 (lambda (x)
	   (case x
	     ((<>) (r2let1 g (gensym)))
	     ((<...>)
	      (let1 g (gensym)
		(unless (null? rest-arg)
		  (error "many rest arg keyword appear *cut-loop* :" xs))
		(set! rest-arg g)
		(values #f g)))
	     (else (values #f x))))
	 xs)
      `(lambda ,(if (null? args)
		  rest-arg
		  (filter identity (append args rest-arg)))
	 ,(expr-trans expr)))))

(define (compose-define-il name ast-name st-name il->slots il-specs struct-id-gen define-il define-ast-traverse-default-handlers)
  `(begin
     ;; struct
     (define ,il-specs (make-hash-table 'eq?))
     ;; (define ,struct-id-gen
     ;;   (let1 c -1
     ;; 	 (lambda () (inc! c))))
     (define (,(symbol-append st-name "-eqv?") a b)
       (and
	(vector? a)
	(vector? b)
	(eq? (il:class a) (il:class b))
	(eqv? (il:id a) (il:id b))))
     (define ,(symbol-append st-name "-copy") vector-copy)
     (define (,(symbol-append st-name "?") a)
       (and (vector? a) (hash-table-exists? (il:class a) ,il-specs)))
     (define-macro (,define-il name slots)
       (define (il:slot-definition-name sd)
	 (if (pair? sd) (car sd) sd))
       (let*-values
	   (((r) (gensym))
	    ((slot-names slot-name-keys)
	     (map2
	      (lambda (s)
		(let1 n (il:slot-definition-name s)
		  (values n (make-keyword n))))
	      slots))
	    ((name:pred) (symbol-append name "?"))
	    ((offset) 2))
	 (define (gen-update-code name target spec . may-be-else-proc)
	   (let ((else-proc (get-optional may-be-else-proc
					  (lambda _ (values #f #f))))
		 (obj (gensym)))
	     (receive (let-vars sset!s)
		 (filter-map2-with-index
		  (lambda (i sd)
		    (let* ((sn (il:slot-definition-name sd))
			   (k (make-keyword sn))
			   (place (+ offset i))
			   (%d (gensym)))
		      (cond
		       ((get-keyword k spec %d)
			(lambda (x) (not (eq? %d x)))
			=> (lambda (x)
			     (let1 g (gensym)
			       (values
				(list g x)
				`(vector-set! ,obj ,place ,g)))))
		       (else (else-proc sn obj place)))))
		  slots)
	       (let1 ill-slots (lset-difference
				eq?
				(kv-list-keys spec)
				slot-name-keys)
		 (unless (null? ill-slots)
		   (errorf "Ast struct ~s does not have slot ~s" name ill-slots)))
	       `(let (,@let-vars (,obj ,target))
		  ,@sset!s
		  ,obj))))
	 `(begin
	    (define-macro (,(symbol-append "make-" name) . spec)
	      `(let ((,',r (make-vector ,',(+ (length slots) offset) #f)))
		 (vector-set! ,',r 0 ',',name)
		 (vector-set! ,',r 1 (,',',struct-id-gen))
		 ,(,gen-update-code
		   ',name ',r spec
		   (lambda (sn obj place)
		     (values
		      #f
		      (cond
		       ((assq sn ',(filter pair? slots))
			=> (lambda (df)
			     `(vector-set! ,obj ,place ,(cadr df))))
		       (else #f)))))))
	    (define-macro (,(il:struct-name->multiple-slot-setter name)
			   target . spec)
	      (,gen-update-code ',name target spec))
	    (define (,name:pred ,r)
	      (and (vector? ,r) (eq? (vector-ref ,r 0) ',name)))
	    (define-macro (,(symbol-append "parent-is-a-" name:pred))
	      `(and (vector? (car *parent-nodes*))
		    (eq? (vector-ref (car *parent-nodes*) 0) ',',name)))
	    ,@(let1 pat `#(class id ,@(map il:slot-definition-name slots))
		`((define-macro (,(symbol-append "decompose-" name) obj)
		    `(match-define ,',pat ,obj))
		  (define-macro
		    (,(symbol-append "let-decompose-" name) obj . body)
		    `(match-let1 ,',pat ,obj ,@body))))
	    ,@(append-map1-with-index
	       (lambda (i sd)
		 (let ((i (+ offset i))
		       (struct (gensym))
		       (nv (gensym))
		       (sn (il:slot-definition-name sd)))
		   `((define ,(il:slot-name->getter name sn)
		       (getter-with-setter
			(lambda (,struct) (vector-ref ,struct ,i))
			(lambda (,struct ,nv) (vector-set! ,struct ',i ,nv))))
		     (define ,(symbol-append (il:slot-name->getter name sn) "*")
		       (getter-with-setter
			(lambda (,struct)
			  (and (,name:pred ,struct) (vector-ref ,struct ,i)))
			(lambda (,struct ,nv)
			  (and (,name:pred ,struct)
			       (vector-set! ,struct ',i ,nv)))))
		     (define-macro (,(il:slot-name->setter name sn)
				    ,struct ,nv)
		       `(begin
			  (vector-set! ,,struct ,',i ,,nv)
			  ,,struct)))))
	       slots))))
     ;; (define (,il-spec-ref struct-name slot-name spec-name)
     ;;   (define (check x p)
     ;; 	 (or x (error #`",il-spec-ref : Unknown parameter :" x)))
     ;;   (let1 struct-spec (check (hash-table-get ,il-specs struct-name #f) struct-name)
     ;; 	 (if (not slot-name)
     ;; 	   struct-spec
     ;; 	   (let1 slot-spec
     ;; 	       (check
     ;; 		(find
     ;; 		 (lambda (x)
     ;; 		   (eq? slot-name (il-spec-slot-name x)))
     ;; 		 struct-spec)
     ;; 		slot-name)
     ;; 	     (if (not spec-name)
     ;; 	       slot-spec
     ;; 	       (vector-ref
     ;; 		slot-spec
     ;; 		(check
     ;; 		 (case spec-name
     ;; 		   ((:name) 0) ((:section) 1) ((:type) 2) ((:struct) 3)
     ;; 		   (else #f))
     ;; 		 spec-name)))))))

     (define-macro (,(symbol-append define-il "s") special-spec . specs)
       (let-keywords
	special-spec
	((common-slots '())
	 (include-classes '()))
	(define (parse-il-def common-slots struct-def)
	  (match-let1
	   (name . struct-specs) struct-def
	   (let-alist*
	    struct-specs eq?
	    ((slot-specs :default '() :key slot)
	     (interslot-specs :default '() :key interslot))
	    (let-keywords
	     interslot-specs
	     ((extra-inherited-attr #f))
	     (when extra-inherited-attr
	       (push! %extra-inherited-attr
		      (cons name extra-inherited-attr))))
	    (cons
	     name
	     (map
	      (lambda (slot-def)
		(let loop ((slot-def slot-def))
		  (if (not (pair? slot-def))
		    (loop (list slot-def))
		    (match-let1
		     (sname . slot-spec) slot-def
		     (let1 sp-init-false (gensym)
		       (let-keywords
			slot-spec
			((section :all) (type :il)
			 (struct :single) (interhandler-ref? #f)
			 (special-init-value sp-init-false)
			 (special-slot-handler #f) (allow-print? #t)
			 (sdf-table? #f) (misc '()))
			(when sdf-table?
			  (let1 s (slot-name->sdf-table-ref sname)
			    (when (memq s *sdf-table-ref-syms*)
			      (errorf "Many definitions that slot ~s contain SDF table are exist." sname))
			    (push!
			     *sdf-table-ref-syms*
			     (cons s (il:slot-name->interhandler-ref-var
				      sname)))))
			(vector sname section type struct
				(or interhandler-ref? sdf-table?)
				special-slot-handler
				(if (eq? special-init-value
					 sp-init-false)
				  (case struct
				    ((:list-list :list) '(list))
				    ((:single) #f)
				    (else (sstruct-error)))
				  special-init-value)
				allow-print? misc)))))))
	      (append common-slots slot-specs))))))
	(let* ((default-update!-handler (make-hash-table 'eq?))
	       (default-no-update-handler (make-hash-table 'eq?))
	       (il-defs (map (cut parse-il-def common-slots <>) specs)))
	  (receive (a b)
	      (map2
	       (lambda (pspec)
		 (match-let1
		  (st-name . slot-defs) pspec
		  (hash-table-put! il-struct-specs st-name slot-defs)
		  (hash-table-put! ,il-specs st-name slot-defs)
		  (receive (no-update-h update!-h)
		      (filter-map2
		       (lambda (sd)
			 (with-decompose-il-slot-spec
			  sd
			  (define (sstruct-error)
			    (error "Unknown struct slot keyword :" st-name sd))
			  (let1 loop-s
			      (case type
				((:il) 'loop-s)
				((:il-or-general)
				 '(lambda (x) (if (il? x) (loop-s x) x)))
				((:il-or-false)
				 '(lambda (x) (and x (loop-s x))))
				((:general) #f)
				(else (sstruct-error)))
			    (let1 sloop
				(cond
				 (sp-shandler `(,sp-shandler ,sname))
				 ((not loop-s) #f)
				 (else
				  (case sstruct
				    ((:list-list)
				     `(map (cut map ,loop-s <>) ,sname))
				    ((:list) `(map ,loop-s ,sname))
				    ((:single) `(,loop-s ,sname))
				    (else (sstruct-error)))))
			      (if sloop
				(values sloop (list (make-keyword sname) sloop))
				(values #f #f))))))
		       slot-defs)
		    (values
		     `(,st-name (*general-form* ,@no-update-h))
		     `(,st-name (*update!* *self* ,@(flat-1 update!-h)))))))
	       (append
		il-defs
		(map
		 (lambda (struct-name)
		   (cond
		    ((hash-table-get il-struct-specs struct-name #f)
		     => (pa$ cons struct-name))
		    (else
		     (error:unknown-il-element struct-name))))
		 include-classes)))
	    `(begin
	       (,',define-ast-traverse-default-handlers no-update ,@a)
	       (,',define-ast-traverse-default-handlers update! ,@b)
	       ,@(map
		  (lambda (pspec)
		    (match-let1
		     (st-name . slot-defs) pspec
		     `(,',define-il ,st-name
			,(filter-map1
			  (lambda (sd)
			    (with-decompose-il-slot-spec
			     sd `(,sname ,init-value)))
			  slot-defs))))
		  il-defs))))))))

(define *extra-component* (make-hash-table 'eq?))

(define-macro (define-external-component name lmd)
  (hash-table-put!
   *extra-component* (symbol-append "use-" name "?")
   (eval lmd (current-module)))
  #t)

(define-macro (define-external-component* name . es)
  `(define-external-component ,name (lambda ,(gensym) ',es)))

(define-macro (multi-push!$ dist) `(for-each$ (lambda (x) (push! ,dist x))))
(define-macro (set!$ dist) `(lambda (x) (set! ,dist x)))

(define (default-*update!*-transformer tag target slot-spec)
  `(,(il:struct-name->multiple-slot-setter tag)
    ,target ,@slot-spec))

(define-macro (component-handler in cspec . es)
  (let*-values
      (((rest) (gensym))
       ((alist-vspec update-spec)
	(map2
	 (lambda (spec-k)
	   (let1 not-e-default (gensym)
	     (let-keywords
	      (cdr spec-k)
	      ((default not-e-default) (struct :sigle) (type :general))
	      (let* ((%proc? (eq? type :proc)) (%list? (eq? struct :list))
		     (%name (car spec-k))
		     (%filter
		      (if %proc?
			(if %list? 'map-check-and-eval 'check-and-eval-car)
			(if %list? 'check-eval-spec
			    '(compose car check-eval-spec)))))
		(when (eq? default not-e-default)
		  (cond
		   (%proc?
		    (error "component-handler : (and (eq? type :proc) (not (exist? :default))) :" spec-k))
		   (%list? (set! default '()))
		   (else (set! default #f))))
		(values
		 `(,%name :default ,default :filter ,%filter)
		 `(list
		   ',%name ,%filter
		   ,(if %list? `(multi-push!$ ,%name) `(set!$ ,%name))))))))
	 cspec)))
    `(let-alist*
      ,in eq? ,(append alist-vspec rest)
      (let* ((_
	      (for-each
	       (lambda (x)
		 (cond
		  ((hash-table-get *extra-component* (car x) #f)
		   => (lambda (gen)
			(let1 ch (list ,@update-spec)
			  (for-each
			   (lambda (x)
			     (and-let* ((h (assq (car x) ch)))
			       (match-let1
				(_ %filter %update!) h
				(%update! (%filter (cdr x))))))
			   (gen (cdr x))))))
		  (else (errorf "external component selector ~s not found."
				(car x)))))
	       ,rest)))
	,@es))))

(define (apply-extra-transformer ets info code)
  (fold (lambda (filter c) (filter info c)) code ets))

(define (compose-ast-traverse name ast-name st-name il->slots il-specs struct-id-gen define-il define-ast-traverse-default-handlers)
  (push! %traverse-macro-name ast-name)
  `(begin
     ;; form traverse
     (define-macro (,define-ast-traverse-default-handlers tag . specs)
       (let1 ht (make-hash-table 'eq?)
	 (for-each
	  (lambda (spec)
	    (hash-table-put! ht (car spec) (cadr spec)))
	  specs)
	 (hash-table-put! *traverse-default-handlers* (cons ',ast-name tag) ht)
	 #f))
     (define (decompose-attr-spec e)
       (match-let1
	(name init update) e
	(values
	 name init
	 (match-map-tree-pre-order2
	  (target update)
	  (handler
	   ('*init* init)
	   ('*inherit* name)
	   mmt:default)))))
     (define-macro (,ast-name . spec)
       (component-handler
	spec
	((use-context? :default #t)
	 (type :default 'update!)
	 (target :default #f)
	 (update! :struct :list)
	 (inherited-attr :struct :list)
	 (synthesized-attr :struct :list)
	 (extra-code:loop  :struct :list)
	 (extra-code:clause :struct :list)
	 (extra-transformer:clause  . #0=(:struct :list :type :proc :default '()))
	 (extra-transformer:loop . #0#)
	 (extra-transformer:traverse . #0#)
	 (macro:*update!* :type :proc :default #f)
	 (macro:*loop* :type :proc :default (lambda (_ x y) (cons x y)))
	 (handler :struct :list))
	(define traverse-default-handlers
	  (let1 key (cons ',ast-name type)
	    (hash-table-keys *traverse-default-handlers*)
	    (hash-table-get*
	     *traverse-default-handlers* key
	     (errorf "~s handlers does not exist!" key))))
	(when use-context?
	  (set! inherited-attr
		`((*parent-nodes* '() (cons *self* *inherit*))
		  ,@inherited-attr)))
	(set! inherited-attr
	      `(,@(fold
		   (lambda (s p)
		     (lset-union
		      (lambda (a b) (eqv? (car a) (car b)))
		      p
		      (assq-ref %extra-inherited-attr s '())))
		   '()
		   (hash-table-keys traverse-default-handlers))
		,@inherited-attr))
	(let-alist*
	 update! eq?
	 ((default-update!-overwrite  :default '() :key *default*))
	 (let-values/init-sequence-bind
	  (((add-self) (lambda (e) `(:self *self* ,@(flat-1 e)))))
	  (((inherited-attr
	     default-loop-spec
	     inherited-attr-init-for-loop
	     inherited-attr-for-named-let
	     inherited-attr-key-only)
	    (values-filter1
	     (map5
	      (lambda (e)
		(receive (name init update) (decompose-attr-spec e)
		  (values
		   (list name init update)
		   (list (make-keyword name) update)
		   (list (make-keyword name) init)
		   (list name init)
		   (make-keyword name))))
	      inherited-attr)
	     #f add-self flat-1 #f (cut cons :self <>)))
	   ((synthesized-attr
	     default-synthesized-spec:init
	     default-synthesized-spec:init-with-no-key
	     default-synthesized-spec:update-with-no-key
	     default-synthesized-spec:key-only)
	    (values-filter1
	     (map5
	      (lambda (e)
		(receive (name init update) (decompose-attr-spec e)
		  (values
		   (list name init update)
		   (list (make-keyword name) init)
		   init update (make-keyword name))))
	      synthesized-attr)
	     #f add-self #f #f #f))
	   ((synthesized-attr-length)
	    (length synthesized-attr))
	   (_
	    (define-mmt-handlers
	      ifu:loop-level-macro
	      (((= (cut assq-ref *sdf-table-ref-syms* <>) table-name)
		. spec)
	       (=> esc) (unless table-name (esc))
	       (set! use-context? #t)
	       (let1 df-df (gensym)
		 (let-keywords
		  spec
		  ((extra-table '()) (context #f) (default df-df))
		  (let* ((context
			  (if context context '(cons *self* *parent-nodes*)))
			 (%find
			  `(lambda (table)
			     (find-and-value
			      (lambda (x) (hash-table-get table (il:id x) #f))
			      ,context))))
		    `(or
		      (,%find ,table-name)
		      (find-and-value ,%find (list ,@extra-table))
		      ,(if (eq? default df-df)
			 `(error
			   ,#`",table-name spec for it, does not exsist :"
			   (map-aid ,context))
			 default)))))))))
	  (define info-for-external-transformer
	    `((inherited-attr . ,inherited-attr)
	      (synthesized-attr . ,synthesized-attr)))
	  (define %apply-extra-transformer
	    (cut apply-extra-transformer <> info-for-external-transformer <>))
	  (define loop-in-traverse (gensym))
	  (define interhandler-ref-vars '())
	  (define (expand-loop-level-macro expr)
	    (match-map-tree-pre-order2
	     (loop-sym loop)
	     (target expr)
	     (handler ifu:safety ifu:loop-level-macro mmt:default)))
	  (define (expand-handler-level-macro tag expr)
	    (define (check-*update!* spec)
	      (if (eq? (car spec) '*update!*)
		(cdr spec)
		'(*self*)))
	    (define (gensym-for-sattr) (gensyms synthesized-attr-length))
	    (let1 current-sattrs (gensym-for-sattr)
	      (define (transform-body expr)
		(define (add-loop-code1 e . exclude-sattr-keys)
		  (define (vector-mask! vec val idxs)
		    (for-each
		     (lambda (i) (vector-set! vec i val))
		     idxs)
		    vec)
		  ;; (define (vector-mask!-not vec val idxs)
		  ;;   (dotimes (i (vector-length vec))
		  ;; 	 (and
		  ;; 	  (not (memv i idxs))
		  ;; 	  (vector-set! vec i val)))
		  ;;   vec)
		  (let*-values
		      (((self) (gensym))
		       ((sattrs1) (gensym-for-sattr))
		       ((mask-idxs)
			(filter-map1
			 (lambda (k)
			   (list-index (cut eq? k <>)
				       default-synthesized-spec:key-only))
			 (get-optional exclude-sattr-keys '())))
		       ((mask!)
			(lambda (sattr)
			  (filter-map2-with-index
			   (lambda (i v)
			     (let1 flag (memq i mask-idxs)
			       (values
				(and (not flag) v)
				(and flag v))))
			   sattr)))
		       ((push!:s1 ex-s1) (mask! sattrs1))
		       ((push!:cs ex-cs) (mask! current-sattrs)))
		    `(receive (,self ,@sattrs1) ,e
		       ,@(map
			  (lambda (cs s1) `(push! ,cs ,s1))
			  push!:cs push!:s1)
		       (values ,self ,@ex-s1))))
		(define (loop-transform loop over-loop-spec . exclude-keys)
		  (macro:*loop*
		   inherited-attr-key-only
		   loop-in-traverse
		   (loop
		    (kv-list-map1
		     (lambda (k v)
		       (match-map-tree-pre-order2
			(target v)
			(handler
			 ifu:safety
			 (('*accum* op val)
			  `(,op ,val ,(keyword->symbol k)))
			 ('*init:loop-args*
			  (get-keyword*
			   k inherited-attr-init-for-loop
			   (error "Unknown loop key :" k)))
			 ('*inherit:loop-args*
			  (keyword->symbol k))
			 mmt:default)))
		     (sort-kv-list
		      (let1 ex (get-optional exclude-keys #f)
			(if (not ex)
			  over-loop-spec
			  (kv-list-filter-append-map1
			   (lambda (k v)
			     (and
			      (not (memq ex k))
			      (list k v)))
			   over-loop-spec)))
		      default-loop-spec)))))
		(let* ((sattrs (gensym-for-sattr))
		       (require-post-process? #f)
		       (result
			(match-map-tree-pre-order2
			 (loop-sym loop) (target expr)
			 (handler
			  (('*next-handler*)
			   `(begin
			      ,@(default-handler-decompose
				  tag
				  (hash-table-get
				   traverse-default-handlers tag))))
			  ifu:safety
			  (('*loop* . over-loop-spec)
			   (add-loop-code1
			    (loop-transform loop over-loop-spec)))
			  (('*loop-with-sattr* . over-loop-spec)
			   (add-loop-code1
			    (loop-transform loop over-loop-spec '(:require))
			    (get-keyword :require over-loop-spec '())))
			  
			  (('*cut-loop* . over)
			   (loop (parse-cut-macro-spec
				  over (cut cons '*loop* <...>))))
			  (('*cut-loop-with-sattr* . over)
			   (loop (parse-cut-macro-spec
				  over (cut cons '*loop-with-sattr* <...>))))
			  (('*cut-update!* . over)
			   (loop (parse-cut-macro-spec
				  over (cut cons '*update!* <...>))))
			  (('*update!* . over)
			   (loop
			    (process-*update!*-macro
			     tag
			     (check-*update!*
			      (hash-table-get traverse-default-handlers tag))
			     over)))
			  (('*map-loop* over-loop-spec filter . vs)
			   (let* ((gvs (gensyms vs))
				  (param '())
				  (user
				   (sort-kv-list
				    over-loop-spec
				    default-loop-spec
				    :exclude-key? #t
				    :default-dist-value
				    (let1 x (gensym)
				      (push! param x)
				      x)
				    :dist-with-no-value? #t)))
			     `(map
			       (lambda (,@gvs)
				 (receive ,(reverse! param)
				     (,(loop filter) ,@gvs)
				   ,(add-loop-code1 `(,loop-in-traverse ,@user))))
			       ,@vs)))
			  (('*synthesize* . over-synthesize-spec)
			   (add-loop-code1
			    `(values
			      ,@(loop
				 (sort-kv-list
				  over-synthesize-spec
				  default-synthesized-spec:init
				  :exclude-key? #t)))))
			  (('*synthesized-ref* . spec)
			   (set! require-post-process? #t)
			   `(*synthesized-ref* ,@spec))
			  ifu:loop-level-macro
			  mmt:default))))
		  (values result require-post-process?)))
	      (let*-values
		  (((pre-body require-post-process?) (transform-body expr))
		   ((result) (gensym)))
		(receive (synthesized-refs-no-set
			  synthesized-refs-set-only
			  synthesized-refs-with-kill)
		    (values-filter1
		     (map3
		      (lambda (ss update init)
			(let ((expr
			       `(fold-right ,update ,init ,ss))
			      (x (gensym)))
			  (values
			   expr
			   `(set! ,ss ,expr)
			   `(begin0
			      ,expr
			      (set! ,ss ,init)))))
		      current-sattrs
		      default-synthesized-spec:update-with-no-key
		      default-synthesized-spec:init-with-no-key)
		     list->vector #f list->vector)
		  (define (transform-body:post expr)
		    (match-map-tree-pre-order2
		     (loop-sym loop)
		     (target expr)
		     (handler
		      ifu:safety
		      (('*synthesized-ref* key . spec)
		       (cond
			((not (keyword? key))
			 (error
			  "*synthesized-ref* : must be keyword. But got " key))
			((list-index (cut eq? key <>)
				     default-synthesized-spec:key-only)
			 => (lambda (i)
			      (let-keywords
			       spec
			       ((with-kill? #f))
			       (vector-ref
				(if with-kill?
				  synthesized-refs-with-kill
				  synthesized-refs-no-set)
				i))))
			(else
			 (errorf "A synthesized attr ~s does not exist." key))))
		      mmt:default)))
		  (let1 body (if require-post-process?
			       (transform-body:post pre-body)
			       (values pre-body '()))
		    `(let* (,@(map (lambda (s _) `(,s '()))
				   current-sattrs
				   ;; dummy
				   default-synthesized-spec:init-with-no-key)
			    (,result
			     (let () ,@body)))
		       ,@synthesized-refs-set-only
		       (values
			,result
			,@current-sattrs)))))))
	  (define (handler-transform tag code)
	    (define (get-il-spec tag)
	      (cond
	       ((hash-table-get ,il-specs tag #f) => identity)
	       (else
		(error:unknown-il-element tag code))))
	    (let-values
		(((slot-decompose ihr-slot-initseq)
		  (filter-map2
		   (lambda (sdef)
		     (let* ((sname (il-spec-slot-name sdef))
			    (get `(,(il:slot-name->getter tag sname)
				   *self*)))
		       (values
			`(,sname ,get)
			(and
			 (il-spec-slot-interhandler-ref? sdef)
			 (let1 ihr-var
			     (il:slot-name->interhandler-ref-var sname)
			   (push! interhandler-ref-vars ihr-var)
			   `(set! ,ihr-var ,sname))))))
		   (get-il-spec tag))))
	      `((,tag)
		,(%apply-extra-transformer
		  extra-transformer:clause
		  `(let* ((id (il:id *self*))
			  (class (il:class *self*))
			  ,@slot-decompose
			  (,(gensym) (begin ,@ihr-slot-initseq)))
		     ,(expand-handler-level-macro
		       tag
		       `((define (loop-s s) (*loop* :self s))
			 ,@extra-code:clause
			 ,@code)))))))
	  (define (process-*update!*-macro tag default over)
	    (let-values
		(((target over)
		  (if (or (null? over) (keyword? (car over)))
		    (values (car default) over) 
		    (values (car over) (cdr over))))
		 ((receiver)
		  (if macro:*update!*
		    macro:*update!*
		    default-*update!*-transformer)))
	      (receiver
	       tag target
	       (kv-list-append-map1
		(lambda (k v)
		  (list
		   k (match-map-tree-pre-order2
		      (target v)
		      (handler
		       ifu:safety
		       ('*inherit:update!* (keyword->symbol k))
		       mmt:default))))
		(marge-kv-list
		 (cdr default)
		 (assq-ref update! tag '())
		 default-update!-overwrite
		 over)))))
	  (define (default-handler-decompose tag dh)
	    (match-let1
	     (handler-type . default-spec) dh
	     (case handler-type
	       ((*update!*)
		(list (process-*update!*-macro tag default-spec '())))
	       ((*general-form*) default-spec)
	       (else
		(error "Bad default handler type in it's spec :" dc)))))
	  (define (compose-default-handler update! handler)
	    (map
	     (lambda (dc)
	       (handler-transform
		(car dc)
		(default-handler-decompose (car dc) (cdr dc))))
	     (lset-difference
	      (lambda (a b) (eq? (car a) (car b)))
	      (hash-table-map traverse-default-handlers cons)
	      handler)))
	  (let*-values
	      (((%else-handler handler)
		(partition (lambda (e) (eq? (car e) 'else)) handler))
	       ((else-handler)
		(cond
		 ((pair? %else-handler)
		  (expand-handler-level-macro
		   'else-handler-dummy-tag
		   (cdar %else-handler)))
		 (else
		  `(error "A object appear without special handler and else clause :" *self* ',spec))))
	       ((handlers0)
		(map
		 (apply$ (lambda (tag . code) (handler-transform tag code)))
		 handler))
	       ((handlers1) (compose-default-handler update! handler))
	       ((ex-code-l) (expand-loop-level-macro extra-code:loop)))
	    (%apply-extra-transformer
	     extra-transformer:traverse
	     `(let ,(map
		     (lambda (v) (list v "interhandler-ref : require init"))
		     interhandler-ref-vars)
		(let ,loop-in-traverse
		  ((*self*
		    ,(or target
			 (error "A target spec must be appear in specs.")))
		   ,@inherited-attr-for-named-let)
		  ,@ex-code-l
		  ,(%apply-extra-transformer
		    extra-transformer:loop
		    `(cond
		      ((vector? *self*)
		       (case (il:class *self*)
			 ,@handlers0
			 ,@handlers1
			 (else ,else-handler)))
		      (else ,else-handler)))))))))))))

(define (compose-args name)
  (let* ((ast-name (symbol-append name "-traverse"))
	 (st-name (symbol-append name "-struct"))
	 (il->slots (symbol-append ast-name "-il->slots"))
	 (il-specs
	  (il:struct-name->struct-specs name))
	 (struct-id-gen
					;(symbol-append st-name "-id-gen")
	  'struct-id-gen)
	 (define-il
	   (symbol-append "define-" st-name))
	 (define-ast-traverse-default-handlers
	   (symbol-append "define-" ast-name "-default-handlers")))
    (values ast-name st-name il->slots il-specs struct-id-gen
	    define-il define-ast-traverse-default-handlers)))

(define-macro (require-intermediate-form-util name)
  (receive rest (compose-args name)
    `(begin
       
       ;; warn
       (define (,(symbol-append name ":warn") x)
	 (format #t "~a : ~a\n" ',name x))
       (define (,(symbol-append name ":warnf") . xs)
	 (format #t "~a : ~a\n" ',name
		 (apply format #f xs)))
       
       ,(apply compose-define-il name rest)
       ,(apply compose-ast-traverse name rest))))

(require-intermediate-form-util tmp)

(define-macro (finish-il-def)
  ;; (hash-table-dump *traverse-default-handlers*)
  (let ((name 'il)
	(trav-name 'il-traverse))
    (let1 ht (make-hash-table 'eq?)
      (hash-table-for-each
       *traverse-default-handlers*
       (lambda (k v) (hash-table-push! ht (cdr k) v)))
      (hash-table-for-each
       ht
       (lambda (k handlers)
	 (let1 type-h (make-hash-table 'eq?)
	   (for-each
	    (cut hash-table-for-each <>
		 (cut hash-table-put! type-h <> <>))
	    handlers)
	   (hash-table-put!
	    *traverse-default-handlers*
	    (cons trav-name k) type-h)))))
    `(begin
       ,(call-with-values (cut compose-args name)
	  (pa$ compose-ast-traverse name))
       ,@(let1 code
	     `(,trav-name
	       (target expr)
	       ;; (use-debug:print-self? :trans identity)
	       (macro:*update!*
		(lambda (tag target sss)
		  (let1 struct-spec
		      (hash-table-get il-struct-specs (x->symbol tag))
		    `(cons
		      (symbol-append ',tag "-" (il:id *self*))
		      (filter-append-map1
		       identity
		       (list
			,@(kv-list-filter-map1
			   (lambda (k x)
			     (with-decompose-il-slot-spec
			      (let1 k (x->symbol k)
				(find
				 (lambda (x)
				   (eq? k (il-spec-slot-name x)))
				 struct-spec))
			      (and
			       allow-print?
			       (or
				(and-let* ((h (get-keyword
					       :special-sexp-trans-handler
					       misc #f)))
				  `(,h ,(caddr x)))
				(let1 bad?
				    (if (eq? :single sstruct)
				      not
				      (any-pred not null?))
				  `(let1 z ,x
				     (match
				      z
				      (((? keyword? _) (? ,bad? _)) #f)
				      ((? ,bad? _) #f)
				      (((? keyword? _) _) z)
				      (else (list z)))))))))
			   sss)))))))
	       (handler
		(else (vector 'else-case *self*)))
	       (update!
		(eval-list
		 (hash-table-map
		  il-struct-specs
		  (lambda (k slot-defs)
		    (cons
		     k
		     (filter-append-map1
		      (lambda (sd)
			(with-decompose-il-slot-spec
			 sd
			 (if (eq? type :general)
			   (let1 k (make-keyword sname)
			     `(,k (list ,k *inherit:update!*)))
			   #f)))
		      slot-defs)))))))
	   `((define (,(symbol-append name "->sexp/ss") expr)
	       (,(car code)
		(use-circular-graph? :require-complement-trans? #t)
		,@(cdr code)))
	     (define (,(symbol-append name "->sexp") expr) ,code)))
       ,@(let1 code
	     `(,trav-name
	       (target x)
	       (macro:*update!*
		(lambda (tag target sss)
		  (let1 ex
		      `(,(il:struct-name->multiple-slot-setter tag)
			(il:copy ,target)
			,@sss)
		    ex)))
	       (handler
		(else *self*)))
	   `((define (,(symbol-append name ":copy*") x) ,code)
	     (define (,(symbol-append name ":copy*/ss") x)
	       ,(list* (car code) '(use-circular-graph?) (cdr code))))))))

(define-external-component circular-graph
  (lambda (rest)
    (let-keywords
     rest
     ((require-complement-trans? #f))
     (let1 memorize-table (gensym)
       `((extra-transformer:loop
	  (lambda (info ex)
	    `(cond
	      ((hash-table-get ,',memorize-table *self* #f) => (apply$ values))
	      (else
	       (hash-table-put!
		,',memorize-table *self*
		(cons *self* ',(map cadr (assq-ref info 'synthesized-attr))))
	       (receive r ,ex
		 (hash-table-put! ,',memorize-table *self* r)
		 (apply values r))))))
	 (extra-transformer:traverse
	  (lambda (_ e)
	    `(let ((,',memorize-table (make-hash-table 'eqv?)))
	       ,(if ,require-complement-trans?
		  `(let1 extra-memorize-table (make-hash-table 'eqv?)
		     (let loop ((x ,e))
		       (cond
			((hash-table-get extra-memorize-table x #f)
			 => identity)
			(else
			 (rlet1
			  r
			  (cond
			   ((il? x)
			    (let1 nx (hash-table-get ,',memorize-table x x)
			      (if (eq? x nx)
				x
				(car nx))))
			   ((pair? x)
			    (car x)
			    (update! (car x) loop)
			    (cdr x)
			    (update! (cdr x) loop)
			    x)
			   (else x))
			  (hash-table-put! extra-memorize-table x r))))))
		  e)))))))))

(define-external-component debug:print-self
  (lambda (rest)
    (let-keywords
     rest
     ((trans 'il->sexp/ss))
     `((extra-transformer:loop
	(lambda (_ c)
	  `(let1 tag (gennum)
	     (begin
	       (format/ss #t "debug:print-self : start-clause ~s ~s\n"
			  tag (,',trans *self*))
	       (receive r ,c
		 (format #t "debug:print-self :   end-clause ~s ~s"
			 tag (length r))
		 (format/ss #t " ~s" (car r))
		 (newline)
		 (apply values r))))))))))

(provide "maeve/compiler/intermediate-language-util")
