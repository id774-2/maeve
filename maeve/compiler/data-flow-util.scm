(define-module maeve.compiler.data-flow-util
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (export-all))
(use file.util)
(current-directory "/home/theo/workspace/maeve")
(select-module maeve.compiler.data-flow-util)

(define (compute-pred&succ:medium e)
  (define (hash-table-filter-push! ht k v)
    (when (and k v) (hash-table-push! ht k v)))
  (let ((pred (make-hash-table 'eqv?))
	(succ (make-hash-table 'eqv?))
	(all-blocks '())
	(tail-block '()))
    (mir-traverse
     (target e) (type no-update)
     (use-circular-graph?)
     (handler
      (block
       (push! all-blocks *self*)
       (*next-handler*))))
    (for-each
     (lambda (b)
       (decompose-block b)
       (hash-table-put! succ id '())
       (hash-table-put! pred id '()))
     all-blocks)
    (for-each
     (lambda (b)
       (decompose-block b)
       (let ((s0 (block-addr:name-of* default-succ))
	     (s1 (block-addr:name-of* opt-succ)))
	 (hash-table-filter-push! succ id s0)
	 (hash-table-filter-push! succ id s1)
	 (hash-table-filter-push! pred s0 id)
	 (hash-table-filter-push! pred s1 id))
       (unless (or default-succ opt-succ)
	 (push! id tail-block)))
     all-blocks)
    (hash-table-dump pred)
    (hash-table-dump succ)
    #?=tail-block
    (values
     (cut hash-table-get pred <> #f)
     (cut hash-table-get succ <> #f))))


(define (bit-vector-for-each proc bit-vec)
  (ultra-iterator () () proc () (:bit-vector bit-vec)))

(define (bit-vector-map->list proc bit-vec)
  (ultra-iterator () (<list>) proc () (:bit-vector bit-vec)))

(define (bit-vector-map->bit-vector proc bit-vec)
  (ultra-iterator () (:bit-vector) proc () (:bit-vector bit-vec)))

(define-values (%make-set! %make-opr2)
  (let1 lv (make-hash-table 'eq?)
    (define (make-one x)
      (case/pred
       x
       (symbol?
	(cond
	 ((hash-table-get lv x #f) => identity)
	 (else (rlet1 r (make-lvar :name x) (hash-table-put! lv x r)))))
       (il? x)
       (else (make-const :v x))))
    (values
     (lambda (d s)
       (make-set! :dist (make-one d) :src (make-one s)))
     (lambda (op v1 v2)
       (make-opr2 :opr op :v1 (make-one v1) :v2 (make-one v2))))))

(define (all-define es)
  (map
   (lambda (e)
     (cond
      ((set!-vls:dists-of* e) => e)
      ((set!:dist-of* e) => e)
      (else '())))
   (block:es-of* es)))

(define (collect-use b)
  (rlet lvars '()
	(mir-traverse
	 (target #?=b) (type no-update)
	 (handler
	  (set!     (loop-s src))
	  (set!-vls (map loop-s src))
	  (lvar (push! lvars *self*))))))

(define (collect-define b)
  (append-map
   (lambda (e)
     (cond
      ((set!-vls:dists-of* e) => identity)
      ((set!:dist-of* e) => list)
      (else '())))
   (block:es-of* b)))

(define-macro (define-df-procedure lmd-lst df-varspec results constraint)
  (define (process-exists css)
    (ultra-iterator
     ()
     (<list>)
     (lambda (cs vs)
       (match
	cs
	(('exists 'def s v)
	 (values
	  (let1 r (gensym)
	    `(rlet1 ,r (collect-use ,s)
		    (update! ,v (pa$ lset-intersection eqv? ,r))
		    (pair? ,r)))
	  (lset-adjoin eqv? vs v)))))
     ('()) css))
  (let ((result (gensym)) (code '()))
    (match-map-tree-pre-order2
     (target constraint)
     (self-sym s)
     (handler
      (((or 'and 'or) . es)
       (receive (es vs) (process-exists es)
       (push! code
	      `(let ,(map (cut list <> '()) vs)
		 (and
		  ,@es
		  (begin
		    ,@(map (lambda (x)
			     `(update!
			       ,result
			       (cut
				,(if (memq x vs) 'lset-union 'lset-adjoin)
				<> ,x)))
			   results)))))))
      mmt:default))
    `(let ((,result '()))
       ,(fold
	 (match-lambda*
	  (((stm b) p)
	   `(for-each (lambda (,stm) ,p) ,b)))
	 `(begin ,@code)
	 df-varspec)
       ,result)))

(%macroexpand
(define-df-procedure (%kill b)
  ((p0 (not b)) (p1 b))
  (p0 x)
  (and
   (exists def p0 x)
   (exists def p1 x))))
(let ((G6523 '()))
  (for-each
   (lambda (p1)
     (for-each
      (lambda (p0)
	(begin
	  (let ((x #f))
	    (and
	     (rlet1 G6524 (collect-use p0)
		    (update! x (pa$ lset-intersection eqv? G6524))
		    (pair? G6524))
	     (rlet1 G6525 (collect-use p1)
		    (update! x (pa$ lset-intersection eqv? G6525))
		    (pair? G6525))
	     (begin (update! G6523 (cut lset-adjoin <> p0))
		    (update! G6523 (cut lset-union <> x)))))))
      (not b)))
   b)
  G6523)

(define-df-procedure (%kill b)
  ((p0 (not b)) (p1 b))
  (p0)
  (and
   (exists def p0 x)
   (exists def p1 x)))

(define-data-flow-expr
  (%use b)
  ((include p b))
  (exists use p x))

(define-data-flow-expr
  (%kill-dash b)
  ((include p b))
  (exists def p x))

(define-data-flow-expr
  (%def b)
  ((include p0 b) (include p1 b))
  (and
   (exists def p0 x)
   (not-exists def p1 x)))

(define (reach b)
  (fold-union
   (p (pred b))
   (union (%def p)
	  (diff (reach p) (%kiil p)))))

(define (live b)
  (union
   (use b)
   (diff
    (fold-union (s (succ b)) (live s))
    (all-define b))))




(let* ((b6 (%make-block '()))
       (b5 (%make-block
	    (%make-set! 'i 2)
	    b6))
       (b4 (%make-block
	    (%make-set! 'j (%make-opr2 '/ 'i 2))
	    b5))
       (b3 (%make-block
	    (%make-set! 'j (%make-opr2 '- 'j 1))
	    b4))
       (b2 (%make-block
	    (%make-set! 'i (%make-opr2 '+ 'i 1))
	    b3))
       (b1 (%make-block
	    (list
	     (%make-set! 'j 10)
	     (%make-set! 'i -8))
	    b2)))
  (%block:opt-succ-set!
   b3 b2 (%make-opr2 '!= 'j 0))
  (%block:opt-succ-set!
   b4 b6 (%make-opr2 '< 'i 8))
  (%block:default-succ-set! b6 b2)
  (let1 x (make-seq :es (list b1 b2 b3 b4 b5 b6))
    (il->graphviz* "nak" x)
     (compute-pred&succ:medium x)
    (process-wait-any #t)))

(provide "maeve/compiler/data-flow-util")