(define-module maeve.lib.gauche.complex-iterator)
(select-module maeve.lib.gauche.complex-iterator)

(use srfi-1)
(use srfi-42)

(define-macro (symbol-append . rest)
  `(string->symbol (string-join (map x->string (list ,@rest)) "")))

(define-macro (gensyms num) `(list-ec (: i 0 ,num) (gensym)))
(define-macro (insert-code* test form) `(if ,test (list ,form) '()))
(define-macro (insert-code  test form) `(if ,test ,form '()))
(define-macro (introspection-args introspection? head? loop-cdr)
  `(if ,introspection?
     `(,,head? (not (pair? (,,loop-cdr lst))))
     '()))
(define-macro (introspection-outer-code introspection? head? x)
  `(if introspection?
     `(let1 ,,head? #t ,,x)
     `(begin ,,x)))

(define (atom? x) (not (pair? x)))

(define-macro (make-foldn kv? left? with-index? introspection? num)
  (let ((head? (gensym))
	(seed (gensyms num))
	(index (gensym))
	(name (symbol-append
	       (if kv? "kv-list-" "")
	       (if introspection? "introspection-" "")
	       (if left? "fold" "fold-right")
	       num
	       (if with-index? "-with-index" "")))
	(loop-cdr (if kv? 'cddr 'cdr)))
    `(begin
       (export ,name)
       (define (,name proc ,@seed lst . more)
	 ,(introspection-outer-code
	   introspection? head?
	   `(if (null? more) ;; (= 1 (length lst))
	      (let loop ((lst ,@(if left?
				  '(lst)
				  '((reverse lst))))
			 ,@(insert-code* with-index? `(,index 0))
			 ,@(map list seed seed))
		(if (atom? lst)
		  (values ,@seed)
		  (call-with-values (cut proc
					 ,@(insert-code* with-index? index)
					 ,@(introspection-args
					    introspection? head? loop-cdr)
					 ,@(cond
					    ((and kv? left?)
					     '((car lst) (cadr lst)))
					    (kv? left?
						 '((cadr lst) (car lst)))
					    (else
					     '((car lst))))
					 ,@seed)
		    (lambda ,seed
		      ,@(insert-code* introspection? `(set! ,head? #f))
		      (loop (,loop-cdr lst)
			    ,@(insert-code* with-index? `(+ 1 ,index))
			    ,@seed)))))
	      (let loop ((lst ,(if left?
				 '(cons lst more)
				 '(map reverse (cons lst more))))
			 ,@(insert-code* with-index? `(,index 0))
			 ,@(map list seed seed))
		(if (any atom? lst)
		  (values ,@seed)
		  (call-with-values (lambda ()
				      (apply
				       proc
				       ,@(insert-code* with-index? index)
				       ,@(introspection-args
					  introspection? head? loop-cdr)
				       ,(cond
					 ((and kv? left?)
					  `(fold-right
					    (lambda (l p)
					      (list* (car l) (cadr l) p))
					    (list ,@seed) lst))
					 (kv?
					  `(fold-right
					    (lambda (l p)
					      (list* (cadr l) (car l) p))
					    (list ,@seed) lst))
					 (else
					  `(fold-right
					    (lambda (e p) (cons (car e) p))
					    (list ,@seed) lst)))))
		    (lambda ,seed
		      ,@(insert-code* introspection? `(set! ,head? #f))
		      (loop (map ,loop-cdr lst)
			    ,@(insert-code* with-index? `(+ 1 ,index))
			    ,@seed)))))))))))

(define (%filter-cons a b) (if a (cons a b) b))

(define-macro (let*-values specs . exprs)
  (fold-right
   (lambda (e body)
     `(receive ,(car e) ,(cadr e) ,body))
   `(begin ,@exprs)
   specs))

(define-macro (make-mapn filter? append? kv? with-index?
			 introspection? split? accum-include? accum-num num)
  (define (add-op op . lst)
    (apply map (pa$ list op) lst))
  (let* ((accum? (not (zero? accum-num)))
	 (name (symbol-append
		(if kv? "kv-list-" "")
		(if filter? "filter-" "")
		(if append? "append-" "")
		(if introspection? "introspection-" "")
		(if split? "split-" "")
		"map" num
		(if accum?
		  (string-append
		   "-accum"
		   (if accum-include? "+" "")
		   (number->string accum-num))
		  "")
		(if with-index? "-with-index" "")))
	 (result (gensyms num))
	 (list-of-result (gensyms num))
	 (rsplit? (gensyms num))
	 (return (gensyms num))
	 (accum (gensyms accum-num))
	 (index (gensym))
	 (head? (gensym))
	 (loop-cdr (if kv? 'cddr 'cdr))
	 (map-cons (if filter? '%filter-cons 'cons))
	 (updates-for-split
	  (if (not split?)
	    '()
	    (map
	     (lambda (result-k list-of-result-k
			       return-k rsplit?-k)
	       `((,result-k ,list-of-result-k)
		 (if ,rsplit?-k
		   (values (,map-cons ,return-k '())
			   (cons ,result-k ,list-of-result-k))
		   (values (,map-cons ,return-k ,result-k)
			   ,list-of-result-k))))
	     result list-of-result return rsplit?)))
	 (let-vars+
	  `(,@(map list accum accum)
	    ,@(insert-code* with-index? `(,index 0))
	    ,@(map (cut list <> '()) result)
	    ,@(insert-code
	       split?
	       (map (cut list <> '()) list-of-result))))
	 (proc-returns
	  (append return accum (insert-code split? rsplit?))))
    (define return-clause
      `(values
	,@(let1 result-filter
	      (if append?
		'(compose (apply$ append) reverse)
		'reverse)
	    (map
	     (lambda (result-k list-of-result-k)
	       (if split?
		 `(reverse!
		   (map
		    ,result-filter
		    (if (null? ,result-k)
		      ,list-of-result-k
		      (cons ,result-k ,list-of-result-k))))
		 `(,result-filter ,result-k)))
	     result list-of-result))
	,@(insert-code accum-include? accum)))
    `(begin
       (export ,name)
       (define (,name proc ,@accum lst . more)
	 ,(introspection-outer-code
	   introspection? head?
	   `(if (null? more) ;; (= 1 (length (cons lst more)))
	      (let loop ((lst lst) ,@let-vars+)
		(if (atom? lst)
		  ,return-clause
		  (let*-values
		      ((,proc-returns
			(proc ,@(insert-code* with-index? index)
			      ,@(introspection-args
				 introspection? head? loop-cdr)
			      ,@(if kv?
				  '((car lst) (cadr lst))
				  '((car lst)))
			      ,@accum))
		       ,@updates-for-split)
		    ,@(insert-code* introspection? `(set! ,head? #f))
		    (loop (,loop-cdr lst)
			  ,@accum
			  ,@(insert-code* with-index? `(+ ,index 1))
			  ,@(if split?
			      result
			      (add-op map-cons return result))
			  ,@(insert-code split? list-of-result)))))
	      (let loop ((lst (cons lst more)) ,@let-vars+)
		(if (any atom? lst)
		  ,return-clause
		  (let*-values
		      ((,proc-returns
			(apply proc ,@(insert-code* with-index? index)
			       ,@(introspection-args
				  introspection? head? loop-cdr)
			       ,(if kv?
				  `(fold-right
				    (lambda (l p)
				      (list* (car l) (cadr l) p))
				    (list ,@accum) lst)
				  '(map car lst))))
		       ,@updates-for-split)
		    ,@(insert-code* introspection? `(set! ,head? #f))
		    (loop (map ,loop-cdr lst)
			  ,@accum
			  ,@(insert-code* with-index? `(+ ,index 1))
			  ,@(if split?
			      result
			      (add-op map-cons return result))
			  ,@(insert-code split? list-of-result)))))))))))
(export make-mapn)

(define-macro (make-for-each kv? with-index? introspection? escape?)
  (define (add-op op . lst)
    (apply map (pa$ list op) lst))
  (let* ((head? (gensym))
	 (index (gensym))
	 (escape-xs (gensym))
	 (name (symbol-append
		(if kv? "kv-list-" "")
		(if introspection? "introspection-" "")
		(if escape? "escape-" "")
		"for-each"
		(if with-index? "-with-index" "")))
	 (loop-cdr (if kv? 'cddr 'cdr)))
    `(begin
       (export ,name)
       (define (,name proc lst . more)
	 ,(introspection-outer-code
	   introspection? head?
	   `(if (null? more) ;; (= 1 (length lst))
	      (let loop ((lst lst)
			 ,@(insert-code* with-index? `(,index 0))
			 ,@(insert-code* escape? `(,escape-xs #f)))
		(cond
		 ,@(insert-code* escape?
				 `(,escape-xs (apply values ,escape-xs)))
		 ((pair? lst)
		  (proc
		   ,@(insert-code* with-index? index)
		   ,@(insert-code* escape? `(lambda xs (set! ,escape-xs xs)))
		   ,@(introspection-args introspection? head? loop-cdr)
		   ,@(if kv?
		       '((car lst) (cadr lst))
		       '((car lst))))
		  ,@(insert-code* introspection? `(set! ,head? #f))
		  (loop (,loop-cdr lst)
			,@(insert-code* with-index? `(+ ,index 1))
			,@(insert-code* escape? escape-xs)))))
	      (let loop ((lst (cons lst more))
			 ,@(insert-code* with-index? `(,index 0))
			 ,@(insert-code* escape? `(,escape-xs #f)))
		(cond
		 ,@(insert-code* escape?
				 `(,escape-xs (apply values ,escape-xs)))
		 ((every pair? lst)
		  (apply
		   proc
		   ,@(insert-code* with-index? index)
		   ,@(insert-code* escape? `(lambda xs (set! ,escape-xs xs)))
		   ,@(introspection-args introspection? head? loop-cdr)
		   ,(if kv?
		      '(fold-right
			(lambda (l p)
			  (list* (car l) (cadr l) p))
			'() lst)
		      '(map car lst)))
		  ,@(insert-code* introspection? `(set! ,head? #f))
		  (loop (map ,loop-cdr lst)
			,@(insert-code* with-index? `(+ ,index 1))
			,@(insert-code* escape? escape-xs)))))))))))

(define-macro (%loop specs . body)
  (let1 r (gensym)
    `(let ((,r '()))
       ,(fold-right
	 (lambda (x prev)
	   (case (car x)
	     ((:bool)
	      `(for-each
		(lambda (,(cadr x)) ,prev)
		'(#t #f)))
	     ((:int)
	      `(do ((,(cadr x) ,(caddr x) (+ ,(cadr x) 1)))
		   ((< ,(cadddr x) ,(cadr x)))
		 ,prev))
	     (else (error "Unkwon spec :" x))))
	 `(push! ,r (begin ,@body))
	 specs)
       (reverse! ,r))))

(define-macro (gen)
  (let* ((*max-value* 5)
	 (r
	  `(begin
	     ,@(%loop
		((:int i 1 *max-value*)
		 (:bool kv?)
		 (:bool left?)
		 (:bool with-index?)
		 (:bool introspection?))
		(list 'make-foldn kv? left? with-index? introspection? i))
	     ,@(%loop
		((:bool filter?)
		 (:bool append?)
		 (:bool kv?)
		 (:bool with-index?)
		 (:bool introspection?)
		 (:bool split?)
		 (:bool accum-include?)
		 (:int accum-num 0 *max-value*)
		 (:int num 1 *max-value*))
		(if (and accum-include? (zero? accum-num))
		  #f
		  (list 'make-mapn filter? append? kv? with-index?
			introspection? split? accum-include? accum-num num)))
	     ,@(%loop
		((:bool kv?)
		 (:bool with-index?)
		 (:bool introspection?)
		 (:bool escape?)
		 (:int i 1 *max-value*))
		(list 'make-for-each kv? with-index? introspection? escape?)))))
    ;;#?=(length r)
    r))

(gen)

;; iterator for keyword-list

(export kv-list->alist kv-list->alist*)

(define (kv-list->alist kv)
  (kv-list-map1 cons kv))

(define (kv-list->alist* kv)
  (kv-list-append-map1 list kv))

(provide "maeve/lib/gauche/complex-iterator")
