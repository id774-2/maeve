(define-module maeve.lib.gauche.misc
  (use srfi-1)
  (use srfi-42)
  (use maeve.lib.gauche.macro-util)
  (use gauche.collection)
  (export-all))

(select-module maeve.lib.gauche.misc)

(define (keyword->symbol k) (string->symbol (keyword->string k)))

(mac
 `(begin
    ,@(let ((v #(first second third fourth fifth sixth seventh eighth ninth ))
	    (r '()))
	(dotimes (i (vector-length v))
	  (push!
	   r `(define (,(string->symbol #`",(vector-ref v i)-value")
		       ,@(list-ec (: i 0 i) '_) x . _)
		x)))
	r)))

(mac
 `(begin
    ,@(let ((v #(first second third fourth fifth sixth seventh eighth ninth ))
	    (r '()))
	(dotimes (i (vector-length v))
	  (push!
	   r `(define (,(string->symbol #`",(vector-ref v i)-value*")
		       . xs)
		(list-ref xs ,i #f))))
	r)))

(define (symbol-append . rest)
  (string->symbol (string-join (map x->string rest) "")))

(define (symbol-join xs . rest)
  (string->symbol
   (apply string-join (map x->string xs) rest)))

(define x->symbol (compose string->symbol x->string))

(define gennum (let1 c -1 (lambda () (inc! c))))

(define (hash-table-find ht pred)
  (find
   (lambda (x) (pred (car x) (cdr x)))
   ht))

(define (hash-table-find-and-value ht pred)
  (let1 r #f
    (find
     (lambda (x) 
       (let1 ? (pred (car x) (cdr x))
	 (when ? (set! r ?))
	 ?))
     ht)
    r))

(define-macro (error-with-output . exprs)
  `(error (with-output-to-string (lambda () ,@exprs))))

(define-macro (hash-table-get* ht key . if-does-not-exist)
  `(cond ((hash-table-get ,ht ,key #f) => identity)
	 (else ,@if-does-not-exist)))

(define-macro (hash-table-dump ht)
  `(begin
     (format #t " ** ~s\n" ',ht)
     (for-each
      (lambda (x) (format #t "~3s : ~s\n" (car x) (cdr x)))
      (hash-table->alist ,ht))))

(define-macro (hash-table-dump* ht . rest)
  (let-keywords
   rest
   ((key-filter identity)
    (value-filter identity)
    (pre-key-filter identity)
    (pre-value-filter identity)
    (<? <)
    (no-title? #f))
   `(begin
      ,@(insert-code* (not no-title?) `(format #t " ** ~s\n" ',ht))
      (for-each
       (lambda (x) (format #t "~3s : ~s\n"
			   (,key-filter (car x))
			   (,value-filter (cdr x))))
       (sort
	(hash-table-map
	 ,ht
	 (lambda (k v)
	   (cons (,pre-key-filter k)
		 (,pre-value-filter v))))
	(lambda (a b) (,<? (car a) (car b))))))))

(define (%il:id k) (vector-ref k 1))

(define (data-flow-table-dump tag ht)
  (define (car< a b) (< (car a) (car b)))
  (format #t "~a :\n" tag)
  (for-each
   (pa$ apply format #t "~s ~s\n") 
   (sort
    (hash-table-map
     ht
     (lambda (k vs)
       (list (%il:id k)
	     (sort (map %il:id vs)))))
    car<))
  ht)

(define (tree-map-merge! dist src)
  (and
   (tree-map? src)
   (tree-map? dist)
   (tree-map-for-each
    src
    (lambda (k v) (tree-map-put! dist k v)))))

(define (tree-map-keys= key= a b)
  (and
   (tree-map? a)
   (tree-map? b)
   (list=
    key=
    (tree-map-keys a)
    (tree-map-keys b))))

(define (hash-table-union! trm k v eq)
  (hash-table-update!
   trm k
   (lambda (vs) (lset-union eq vs v))
   '()))

(define (hash-table-update-all! src proc . rest)
  (let-keywords
   rest
   ((dist src) (key-filter identity) (default #f))
   (hash-table-for-each
    src
    (lambda (k v)
      (hash-table-update!
       dist (key-filter k)
       (if (eq? src dist)
	 (lambda _ (proc k v))
	 (cut proc k v <>))
       default)))))

(define (hash-table-copy ht)
  (rlet1
   nht (make-hash-table (hash-table-type ht))
   (hash-table-update-all!  
    ht
    (lambda (_ v _) v)
    :dist nht)))

(define (hash-table-merge! dist srcs)
  (for-each
   (lambda (s)
     (hash-table-for-each s (lambda (k v) (hash-table-put! dist k v))))
   srcs)
  dist)

(define-macro (call-and . xs)
  (let*-values
      (((arg1 procs) (last+others xs))
       ((rvar vspec)
	(fold-right2
	 (lambda (proc pv seq)
	   (rlet* ((g (gensym))
		   (_ `((,g (,proc ,pv)) ,@seq)))))
	 arg1 '() procs)))
    `(and-let* ,(reverse! vspec) ,rvar)))

(define-macro (or-call . thunks) `(or ,@(map list thunks)))

(define (every$ pred) (pa$ every pred))
(define (any$ pred) (pa$ any pred))

(provide "maeve/lib/gauche/misc")
