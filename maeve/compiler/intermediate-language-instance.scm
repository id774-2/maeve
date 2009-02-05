(define-module maeve.compiler.intermediate-language-instance
  (use maeve.compiler.intermediate-language-util)
  (export-all))

(select-module maeve.compiler.intermediate-language-instance)

(define (trans-il-in-list loop-s code)
  (match-map-tree-pre-order2
   (target code)
   (handler
    ((? il? e) (loop-s e))
    mmt:default)))

(define-macro (sel-mod-for-handler module)
  (let1 mod (gensym)
    `(let1 ,mod ,module
       (set! %current-module-table
	     (and (mod? ,mod) (mod:table-of ,mod)))
       (set! %current-module ,mod))))

(define-macro (with-mod-for-handler module . body)
  (let1 pcm (gensym)
    `(let1 ,pcm %current-module
       (dynamic-wind
	   (lambda () (sel-mod-for-handler ,module))
	   (lambda () ,@body)
	   (lambda () (sel-mod-for-handler ,pcm))))))

(require-intermediate-form-util mir)

(define-macro (%make-deflabel lbl e . opt-place)
  (let ((%d (gensym)) (%lbl (gensym)))
    `(let* ((,%lbl ,lbl)
	    (,%d (make-deflabel
		  :lbl ,%lbl :e ,e :place ,(get-optional opt-place #f))))
       (hash-table-put! *definitions* ,%lbl ,%d)
       ,%d)))

(define-mir-structs
  ()
  (cunit (slot
	  (modules :struct :list :allow-print? #f)
	  (large-consts :struct :list)
	  (entry-point :type :il-or-false)
	  (init-point :type :il-or-false)
	  (definitions :type :general
	    :special-init-value (make-hash-table 'eqv?)
	    :interhandler-ref? #t :allow-print? #f)
	  (es :struct :list
	      :special-slot-handler (cut seqflat <> loop-s))))
  (block (slot
	  (es :struct :list)
	  (default-succ :type :il-or-false)
	  (opt-succ :type :il-or-false)
	  (test :type :il-or-false)
	  ;;(succs :struct :list :misc (:check (every$ jump-if?)))
	  ))
  (block-addr (slot (name :type :general)))
;;   (jump-if (slot (test :type :il-or-false
;; 		       :misc (:check (any-pred value-element? opr2?)))
;; 		 tgt))
  (seq (slot (es :struct :list)))
  (deflabel (slot (lbl :misc (:check label?)) (e :type :il-or-false)
		  (place :type :general)))
  (label (slot (name :type :general)
	       (module :allow-print? #f :type :il-or-false
		       :misc (:check module?))))
  (lmd (slot (param :struct :list :misc (:check (every$ lvar?)))
	     (local-vars :struct :list :misc (:check (every$ lvar?)))
	     (rest-arg? :type :general)
	     (es :struct :list
		 :special-slot-handler (cut seqflat <> loop-s))))
  (lvar (slot (name :type :general)))
  (svar (slot (type :type :general)))
  (result (slot (num :type :general)))
  (register (slot (num :type :general)))
  (const (slot (v :type :general)))
  (call (slot (proc :misc (:check value-element?))
	      (args :struct :list :misc (:check (every$ value-element?)))
	      (tail-ctx? :type :general)))
  (mem (slot (base :misc (:check value-element?))
	     (offset :type :general)))
  (elt (slot s e))
  (set!-vls
   (slot (dists :struct :list)
	 (src :misc (:check (any-pred call? value-element? vls?)))))
  (vls (slot (es :struct :list
		 :misc (:check (every$ (any-pred call? value-element?))))))
  (set! (slot dist (src :misc (:check (any-pred call? value-element?)))))
  (opr2 (slot (opr :type :general)
	      (v1 :misc (:check value-element?))
	      (v2 :misc (:check value-element?))))
  
  (dummy-test (slot (opr :type :general)))
  (opr1 (slot (opr :type :general) (v :misc (:check value-element?))))
  (foreign-code
   (slot
    (name :type :general)
    (code :type :general
	  :special-slot-handler (cut trans-il-in-list loop-s <>))))
  (with-mod
   #0=(interslot :extra-inherited-attr
		 ((%current-module #f *inherit*)
		  (%current-module-table #f *inherit*)))
   (slot (module :misc (:check module?))
	 (body :special-slot-handler
	       (lambda (x) (with-mod-for-handler module (loop-s x))))))
  (sel-mod
   #0#
   (slot (module :special-slot-handler
		 (lambda (x) (sel-mod-for-handler x) (loop-s x))
		 :misc (:check module?))))
  (mod
   (slot
    (name  :type :general)
    (imported-modules :struct :list :allow-print? #f)
    (imported-labels :type :general :special-init-value '() :allow-print? #f)
    (exported-labels :type :general :special-init-value '() :allow-print? #f)
    (table :type :general :allow-print? #f))))

(require-intermediate-form-util internal-interface)

(define-internal-interface-structs
  ()
  (register-allocation-result
   (slot
    (compute-using-register
     :type :general :special-init-value (lambda (parent-nodes) (error "compute-using-register was not initialized.")))
    (lvar-allocation
     :type :general :special-init-value (lambda (parent-nodes lvar) (error "lvar-allocation was not initialized.")))))
  (compute-pred&succ-result
   (slot
    (pred :type :general)
    (succ :type :general)
    (stm-pred :type :general)
    (stm-succ :type :general)
    (tail-blocks :struct :list)
    (id->block  :struct :list)))
  (rd-elm
   (slot
    dist src (num :type :general)))
  (live-elm
   (slot var (end? :type :general))))

(finish-il-def)

(define (seqflat-all xs)
  (let1 flatted? #t
    (while flatted?
      ;; (set!-values (xs flatted?) (seqflat xs))
      (receive (x y) (seqflat xs)
	(set! flatted? y) (set! xs x)))
    xs))

(define (seqflat xs . proc)
  (unless (or (null? xs) (pair? xs))
    (error "seqflat : list required, but got " xs))
  (let* ((flatted? #f)
	 (p (get-optional proc identity))
	 (x (append-map1
	     (lambda (x)
	       (let1 x (p x)
		 (case/pred
		  x
		  (seq?
		   (set! flatted? #t)
		   (seq:es-of x))
		  (else (list x)))))
	     xs)))
    (values x flatted?)))

;; (define (jump-if=? x y)
;;   (il:eqv? (jump-if:tgt-of y) (jump-if:tgt-of x)))
;; (define (make-jump-if-to-block block-or-id . opt-test)
;;   (make-jump-if
;;    :test (get-optional opt-test #f)
;;    :tgt (%make-block-addr block-or-id)))
;; (define (block:succs-cons x xs)
;;   (if (member x xs jump-if=?) xs (cons x xs)))
;; (define (block:succs-push! block x)
;;   (update! (block:succs-of block) (cut block:succs-cons x <>))
;;   block)
;; (define (no-test-jump? e) (and (jump-if? e) (not (jump-if:test-of e))))
;; (define (block-has-no-test-jump? block)
;;   (and (block? block) (find no-test-jump? (block:succs-of block))))

(define (%block:default-succ-set! self tgt)
  (block:default-succ-set! self (%make-block-addr tgt)) self)

(define (%block:opt-succ-set! self tgt test)
  (block:slot-set!* self :opt-succ (%make-block-addr tgt) :test test) self)

(define (block-has-not-succ? b)
  (and
   (block? b) (not (block:default-succ-of b)) (not (block:opt-succ-of b))
   (if (block:test-of b)
     (error "Invalid block( !has-opt-succ && has-test) (1st)" b)
     #t)))

(define (block:succs-copy! dist src)
  (when (block? src)
    (block:slot-set!* 
     dist :test (block:test-of src)
     :opt-succ (block:opt-succ-of src)
     :default-succ (block:default-succ-of src)))
  dist)

(define (%make-block es . rest-succ)
  (let-optionals* rest-succ
      ((ds #f) (t #f) (os #f))
    (when (xor t os)
      (error "%make-block : mallformed spec " `(%make-block ,es ,@rest-succ)))
    (make-block
     :es (if (list? es) es (list es)) :test t
     :default-succ (and ds (%make-block-addr ds))
     :opt-succ (and os (%make-block-addr os)))))

(define (%make-block-addr block-or-id)
  (make-block-addr
   :name (case/pred
	  block-or-id
	  (block? (il:id block-or-id))
	  (integer? block-or-id)
	  (else (error "block or integer required, but got :" block-or-id)))))

(define (block-has-opt-succ? b)
  (and
   (block? b) (block:opt-succ-of b)
   (case/pred
    (block:test-of b) 
    ((opr2? dummy-test?) #t)
    (else (error "Invalid block( !has-opt-succ && has-test) (2nd)" b)))))

(define (block-has-no-test-jump? b)
  (and (block? b) (block:default-succ-of b)))

(define (block:es-append-post! block es)
  (update! (block:es-of block) (cut append <> es))
  block)

(define (lmd:block-delete! lmd block)
  (update! (lmd:es-of lmd) (remove$ (cut il:eqv? block <>)))
  lmd)

(define-macro (%seqhandler) `(cut map-seqflat loop-s <>))

(define *dprint-counter* -1)

(mac
 `(begin
    ,@(append-map1
       (match-lambda
	((pret trans)
	 `((define (,pret r . rest)
	     (apply pretty-print (,trans r) rest)
	     r)
	   (define-macro (,(string->symbol #`"debug:,pret") tag r . rest)
	     `(let1 n (inc! *dprint-counter*)
		(format #t "** start : ~a ~a\n" ,tag n)
		(rlet1 r ,r
		       (format #t "** end : ~a ~a\n" ,tag n)
		       (apply pretty-print
			      (if (pair? r)
				(map ,',trans r)
				(,',trans r))
			      ,rest)))))))
       '((il:pp/ss il->sexp/ss)
	 (il:pp    il->sexp)))))

(define il-set-union (cut lset-union/save-order il:eqv? <...>))
(define il-set-adjoin (cut lset-adjoin/save-order il:eqv? <...>))

(define small-const-type? (any-pred number? boolean? char? null?))
(define large-const-type? (any-pred pair? vector? string?))

(define (large-const-element? e)
  (and (const? e) (large-const-type? (const:v-of e))))
(define (small-const-element? e)
  (and (const? e) (small-const-type? (const:v-of e))))

(define value-element?
  (any-pred lvar? label? const? mem? result? svar? register?))

(define (make-misc-const x) (make-const :v ((make-misc-immidiate) x)))

(define (ili:multi-push/pop xs . opt-dists)
  (let* ((opt-dists (get-optional opt-dists '()))
	 (len-ods (length opt-dists))
	 (len-xs (length xs))
	 (n (if (> len-ods len-xs)
	      0
	      (- len-xs len-ods)))
	 (vs (variable-size))
	 (pre  '(((set! t 0))))
	 (post '(((set! t 0)))))
    (receive (opt-dists-src other-src)
	(if (> len-ods len-xs)
	  (values xs '())
	  (split-at xs len-ods))
      (define (%make make-set)
	`(seq
	  ,@(append
	     (map
	      (lambda (d s) (make-set d s))
	      opt-dists opt-dists-src)
	     (map1-with-index
	      (lambda (i x) (make-set `(mem (svar sp) ,(* vs i)) x))
	      other-src))))
      (values
       (* n vs)
       (%make (lambda (d s) `(set! ,d ,s)))
       (%make (lambda (s d) `(set! ,d ,s)))))))

(define (ili:push/pop-all-registers)
  (ili:multi-push/pop
   (unfold
    zero?
    (lambda (x) `(register ,(- x 1)))
    (cut - <> 1)
    (num-of-registers))))

(define (ili:with-register-save body)
  (receive (n pre post) (ili:push/pop-all-registers)
    `(seq
      (dec! (svar sp) ,n)
      ,pre ,@body ,post
      (inc! (svar sp) ,n))))

(define (rregister->regnum x)
  (cond
   ((vector-index (pa$ eq? x) (registers)) => identity)
   (else (errorf "real register ~s does not exists in ~s." x (registers)))))

(set!
 x86-64:make-call-c-function
 (lambda (func args)
   (receive (m prepare-args _)
       (ili:multi-push/pop args (map
				 (lambda (x)
				   `(register ,(rregister->regnum x)))
				 '(rdi rsi rdx rcx r8 r9)))
     (ili:with-register-save
      `((dec! (svar sp) ,m)
	,prepare-args
	(set! (register 0) 0)
	(gas-form ,#`"call ,|func|\n")
	(inc! (svar sp) ,m))))))

(set!
 x86-32:make-call-c-function
 (lambda (func args)
   (receive (m prepare-args _) (ili:multi-push/pop args)
     (ili:with-register-save
      `((dec! (svar sp) ,m)
	,prepare-args
	(set! (register 0) 0)
	(gas-form ,#`"call ,|func|\n")
	(inc! (svar sp) ,m))))))

;; (use srfi-43)

;; (let ((args '(x y))
;;       (regs '#(rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r14 r15)))
;;   (format #t "add $~a, %rsp\n" (* 8 (+ (vector-length regs) (length args))))
;;   (let ((push-seq '()) (pop-seq '()))
;;     (vector-for-each
;;      (lambda (i x)
;;        (push! push-seq (format #f "mov ~a(%rsp), %~a\n" (* i 8) x))
;;        (push! pop-seq  (format #f "mov %~a, ~a(%rsp)\n" x (* i 8))))
;;      regs)
;;     (values push-seq pop-seq)))
;; add $128, %rsp
;; mov %rax, 0(%rsp)
;; mov %rbx, 8(%rsp)
;; mov %rcx, 16(%rsp)
;; mov %rdx, 24(%rsp)
;; mov %rsi, 32(%rsp)
;; mov %rdi, 40(%rsp)
;; mov %r8, 48(%rsp)
;; mov %r9, 56(%rsp)
;; mov %r10, 64(%rsp)
;; mov %r11, 72(%rsp)
;; mov %r12, 80(%rsp)
;; mov %r13, 88(%rsp)
;; mov %r14, 96(%rsp)
;; mov %r15, 104(%rsp)
;; #<undef>

	     
(define-macro (%graphviz-out . es)
  `(with-string-io
       (with-output-to-string
	 (lambda () (begin ,@es)))
     (lambda ()
       (port-for-each
	(lambda (c)
	  (case c
	    ((#\newline) (display "\\l"))
	    ((#\") (display "\\\""))
	    (else (write-char c))))
	read-char))))

(define (il->graphviz e)
  (define nodes (make-hash-table 'equal?))
  (define edges '())
  (mir-traverse
   (target e)
   (inherited-attr
    (pred-block-name #f #f))
   (type no-update) (use-circular-graph?)
   (handler
    (block
     (define block-name #`"block_,id")
     (define (push!-edge test tgt)
       (when tgt
	 (push! edges
		(vector
		 block-name
		 (let loop ((tgt tgt))
		   (case/pred
		    tgt
		    (label? #`"label_,(il:id tgt)")
		    (block-addr? #`"block_,(block-addr:name-of tgt)")
		    (mem? #`",(loop (mem:base-of tgt))")
		    (else (error "il->graphviz : jump target :" tgt))))
		 (if test (%graphviz-out (il:pp test :width 10)) "")))))
     (for-each loop-s es)
     (hash-table-put!
      nodes block-name
      (%graphviz-out
       (format #t "block ~a\n\n" block-name)
       (for-each (cut il:pp <> :width 50) es)))
     (push!-edge #f default-succ)
     (push!-edge test opt-succ))))
  (print "digraph cfg {")
  (print "  edge [fontsize = \"10\"];")
  (print "  graph[margin=\"1\"];")
  (print "  node [shape = \"box\", fontsize = \"10\", width=\"5\"];")
  (hash-table-for-each
   nodes
   (lambda (k v) (format #t "~a [ label = \"~a\"];\n" k v)))
  (for-each
   (match-lambda
    (#(pred succ test)
     (format #t "~a -> ~a [label = \"~a\"];\n" pred succ test)))
   edges)
  (print "}")
  e)

(define (il->graphviz* omn x)
  (with-output-to-graphviz-file
   omn (il->graphviz x))
  (run-process
   `("dot" "-Tgif" "-o"
     ,(omn->graphviz-object-file omn)
     ,(omn->graphviz-file omn)))
  x)

(provide "maeve/compiler/intermediate-language-instance")
