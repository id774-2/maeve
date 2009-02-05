(define-module maeve.lib.gauche.list-util
  (use srfi-1)
  (use util.match)
  (use maeve.lib.gauche.values)
  (use maeve.lib.gauche.complex-iterator)
  (use maeve.lib.gauche.macro-util)
  (export-all))

(select-module maeve.lib.gauche.list-util)

(define (length=1? xs) (and (pair? xs) (null? (cdr xs))))
(define (length>2? xs) (and (pair? xs) (not (null? (cdr xs)))))

(define (last+others xs)
  (let loop ((xs xs) (rs '()))
    (if (length=1? xs)
      (values (car xs) (reverse! rs))
      (loop (cdr xs) (cons (car xs) rs)))))

(define (find-and-value pred lst)
  (let loop ((xs lst))
    (cond
     ((null? xs) (values #f #f))
     ((pred (car xs)) => (cut values <> #t))
     (else (loop (cdr xs))))))

(define (find-and-others pred lst)
  (let loop ((xs lst) (pre '()))
    (cond
     ((null? xs) (values #0=(reverse! pre) #f '()))
     ((pred (car xs)) (values #0# (car xs) (cdr xs)))
     (else (loop (cdr xs) (cons (car xs) pre))))))

;; (define (find+remove pred xs)
;;   (let loop ((xs xs) (rs '()))
;;     (cond
;;      ((null? xs) (values #f xs))
;;      ((pred (car xs))
;;       (values (car xs) (append-reverse rs (cdr xs))))
;;      (else;;       (loop (cdr xs) (cons (car xs) rs))))))
;; (define (last-cons! xs x)
;;   (set-cdr! (last-pair xs) (list x)))

(define flat-1 (apply$ append))

(define (flatten xs)
  (let loop ((x xs))
    (cond
     ((pair? x) (append-map1 loop x))
     ((null? x) '())
     (else (list x)))))

(define (append+ a b)
  (define (pred x)
    (or (pair? x) (null? x)))
  (let ((_a (pred a)) (_b (pred b)))
    (cond
     ((and _a _b) (append b a))
     (_a `(,b ,@a))
     (_b `(,@b ,a)))))

(define (false->nil x) (if x x '()))
(define (false->x x d) (if x x d))

(define (filter-list . xs) (filter identity xs))
(define (filter-cons x xs) (if x (cons x xs) xs))
(define (filter-append1 xs x) (if x `(,@xs ,x) xs))
(define (filter-list* . xs)
  (if (null? xs)
    '()
    (let loop ((xs xs))
      (if (null? (cdr xs))
	(car xs)
	(filter-cons (car xs) (loop (cdr xs)))))))

(define (filter*-cons x xs)
  (if (or (null? x) (not x))
    xs
    (cons x xs)))
(define (filter*-list . xs)
  (fold-right filter*-cons '() xs))

(define (filter*-append1 xs x)
  (if (or (null? x) (not x))
    xs
    `(,@xs ,x)))
(define (filter*-list* . xs)
  (if (null? xs)
    '()
    (let loop ((xs xs))
      (if (null? (cdr xs))
	(false->nil (car xs))
	(filter*-cons (car xs) (loop (cdr xs)))))))

(define (lset-adjoin/save-order eq lst e)
  (if (member e lst eq) lst (cons e lst)))

(define (lset-union/save-order eq . lsts)
  (fold (fold-right$ (lambda (e l)
		       (lset-adjoin/save-order eq l e)))
	'() lsts))

(define (kv-list? xs)
  (let loop ((xs xs))
    (or (null? xs)
	(and (keyword? (car xs)) (pair? (cdr xs))
	     (loop (cddr xs))))))

(define kv-list-keys   (cut kv-list-map1 (lambda (k _) k) <>))
(define kv-list-values (cut kv-list-map1 (lambda (_ v) v) <>))

(define (marge-kv-list . dist-src1-src2...srck)
  (define (marge1 dist src)
    (cond
     ((null? src) dist)
     ((null? dist) src)
     (else
      (append
       (append-map1
	(lambda (k) (list k (get-keyword k dist)))
	(lset-difference
	 eq?
	 (kv-list-map1
	  (lambda (k _) k)
	  dist)
	 (kv-list-map1
	  (lambda (k _) k)
	  src)))
       src))))
  (fold-right marge1 '() dist-src1-src2...srck))

(define-macro (define-keywords rest vspec)
  (let ((vs (map car vspec))
	(nvspec (map (lambda (x) (cons (gensym) (cdr x))) vspec)))
    `(begin
       ,@(map (cut list 'define <> #f) vs)
       (let-keywords
	,rest ,nvspec
	,@(map (lambda (v nv) `(set! ,v ,(car nv))) vs nvspec)))))

(define-macro (sort-kv-list dist sort-spec . extra)
  (with-variables*
   (k v) (gensym)
   (let-keywords
    extra
    ((exclude-key? #f) (default-dist-value v) (dist-with-no-value? #f))
    `(,(if exclude-key? kv-list-map1 kv-list-append-map1)
      (lambda (,k ,v)
	,(let1 get
	     (if dist-with-no-value?
	       `(if (memq ,k ,dist)
		  ,default-dist-value
		  ,v)
	       `(get-keyword ,k ,dist ,default-dist-value))
	   (if exclude-key?
	     get
	     `(list ,k ,get))))
      ,sort-spec))))

;; (sort-kv-list '(:a 0 :b 1 :c 2) '(:b 9 :c 8 :d 7 :e 6))
;; ;; => (:b 1 :c 2 :d 7 :e 6)

;; (sort-kv-list '(:b :d :c :e) '(:a 0 :b 1 :c 2)
;; 	      :exclude-key? #t
;; 	      :default-dist-value #f
;; 	      :dist-with-no-value? #t)
;; ;; => (0 #f #f)

(define-macro (let-alist* alst eq vars . body)
  (with-variables*
   (xs xa dummy) (gensym)
   (let1 rest
       (cond
	((cdr (last-pair vars)) symbol? => (lambda (x) x))
	(else (gensym)))
     (receive (vars updates)
	 (map2
	  (lambda (spec)
	    (let ((var (car spec)))
	      (let-keywords
	       (cdr spec)
	       ((key var) (default #f) (filter identity))
	       (values
		(list var default)
		`(and
		  (,eq ',key ,xa)
		  (begin (set! ,var (,filter (cdr ,xs))) #t))))))
	  vars)
       `(let* (,@vars
	       ;; hack for "syntax-error" about internal define.
	       (,rest '())
	       (,dummy
		(for-each
		 (lambda (,xs)
		   (and (pair? ,xs)
			(let1 ,xa (car ,xs)
			  (or ,@updates (push! ,rest ,xs)))))
		 ,alst)))
	  ,@body)))))

;; (define-macro (let-alist alst eq vars . body)
;;   (let ((xs (gensym)) (xa (gensym)) (dummy (gensym))
;; 	(rest
;; 	 (cond
;; 	  ((cdr (last-pair vars)) symbol? => (lambda (x) x))
;; 	  (else (gensym)))))
;;       (receive (vars updates)
;; 	  (map2
;; 	   (lambda (v)
;; 	     (receive (v key lv)
;; 		 (match
;; 		  v
;; 		  ((v k)
;; 		   (values v k (list v #f)))
;; 		  ((v k d)
;; 		   (values v k (list v d)))
;; 		  (else
;; 		   (values v v (list v #f))))
;; 	       (values
;; 		lv
;; 		`(and
;; 		  (,eq ',key ,xa)
;; 		  (begin (set! ,v (cdr ,xs)) #t)))))
;; 	   vars)
;; 	`(let* (,@vars
;; 		(,rest '())
;; 		;; hack for "syntax-error" about internal define.
;; 		(,dummy
;; 		 (for-each
;; 		  (lambda (,xs)
;; 		    (and (pair? ,xs)
;; 			 (let1 ,xa (car ,xs)
;; 			   (or ,@updates
;; 			       (push! ,rest ,xs)))))
;; 		  ,alst)))
;; 	   ,@body))))

(provide "maeve/lib.gauche/list-util")
