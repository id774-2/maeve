(define-module maeve.lib.gauche.ultra-iterator
  (use util.list)
  (use srfi-1)
  (use srfi-11)
  (use srfi-13)
  (use srfi-42)
  (use gauche.sequence)
  (export ultra-iterator symbol-append
	  make-bit-vector bit-vector-set* bit-vector-set
	  bit-vector-reset bit-vector-null? bit-vector-next
	  bit-vector-intersection bit-vector-union bit-vector-pp))
(select-module maeve.lib.gauche.ultra-iterator)

(define-macro (insert-code* x y) `(if ,x (list ,y) '()))
(debug-print-width 10000)

;; memo 
;; missing general-option ()
;; missing fold-option (left?)
;; missing map-option (split?)
;; missing for-each-option ()
;; missing i/o-type (integer? hash-table?)

(define (make-bit-vector size) (expt 2 size))
(define (bit-vector-set*  vec idx v) (copy-bit idx vec  v))
(define (bit-vector-set   vec idx)   (copy-bit idx vec #t))
(define (bit-vector-reset vec idx)   (copy-bit idx vec #f))
(define (bit-vector-null? n) (= 1 n))
(define (bit-vector-next  n)
  (values (logand 1 n) (ash n -1)))
(define bit-vector-intersection logand)
(define bit-vector-union logior)
(define (bit-vector-pp x)
  (format #t "#,(bit-vector ~b)\n" x)
  x)

(define (symbol-append . rest)
  (string->symbol (string-join (map x->string rest) "")))

(define-macro (with-gensyms vs . es)
  `(let ,(map (cut list <> '(gensym)) vs) ,@es))

(define (fold-right3-with-index proc r0 r1 r2 xs)
  (let loop ((xs (reverse xs)) (i 0) (r0 r0) (r1 r1) (r2 r2))
    (if (null? xs)
      (values r0 r1 r2)
      (receive (r0 r1 r2) (proc i (car xs) r0 r1 r2)
	(loop (cdr xs) (+ 1 i) r0 r1 r2)))))

(define (gensyms x)
  (cond
   ((list? x) (map (lambda _ (gensym)) x))
   (else
    (error "invalid gensyms input :" x))))

(define-macro (if-gensym test)
  `(if ,test (gensym) #f))

(define map-list (map$ list))

(define (filter-let-lvar-spec . xs)
  (filter car (slices xs 2)))

(define-macro (let-keywords+ rest vspec . es)
  (with-gensyms
   (val str r flag)
   `(let-keywords
     ,rest (,@vspec . ,r)
     (let loop ((,r ,r) (,str "") (,val ""))
       (let ((,flag #f))
	 ,@(map
	    (lambda (v)
	      `(cond
		((regexp-replace-all
		  ,(string->regexp
		    (regexp-quote
		     (x->string (car v))))
		  ,str
		  (lambda _ (set! ,flag #t) ""))
		 (lambda _ ,flag)
		 => (lambda (,r)
		      (set! ,flag #f)
		      (set! ,str ,r)
		      (set! ,(car v) ,val)))))
	    vspec))
       (when (string-index ,str #[^-])
	 (error "invalid residual string :" ,str))
       (unless (null? ,r)
	 (loop (cddr ,r) (x->string (car ,r)) (cadr ,r))))
     ,@es)))


;; (let-keywords+
;;  '(:escape?-filter? #t)
;;  ((escape? #f) (filter? #f) (index? #f))
;;  (values escape? filter? index?))
;; => #t #t #f

(define class? (cut is-a? <> <class>))

(define *specs* '(escape? filter? index? append? kv? introspection? dict
			  bit-vector))
(define-macro (let-decompose-spec options . es)
  `(let-keywords+ ,options ,(map (cut list <> #f) *specs*) ,@es))

(define-macro (parse-input idx options)
  (define local-spec (cut symbol-append "%" <>))
  (define local-specs (map local-spec *specs*))
  `(let-keywords+
    ,options
    ,(map (lambda (ls gs) (list ls (make-keyword gs) #f))
	  local-specs *specs*)
    ,@(map (lambda (gs ls)
	     `(when ,ls
		(when (eqv? ,ls #t)
		  (set! ,ls ,idx))
		(cond
		 ((or (pair? ,gs) (null? ,gs)) (push! ,gs ,ls))
		 ((not ,gs) (set! ,gs (list ,ls)))
		 (else (set! ,gs (list ,ls ,gs))))))
	   *specs* local-specs)))

(define-macro (ultra-iterator options output-specs proc fold-seeds . input-specs)
  (define (require-component? i x?)
    (cond
     ((integer? x?) (= i x?))
     ((pair? x?) (memv i x?))
     (else x?)))
  (define (err:output-spec os)
    (error "Bad output spec :" os))
  (let-decompose-spec
   options
   (update!
    input-specs
    (pa$ map-with-index
	 (lambda (i e)
	   (if (and (pair? e) (keyword? (car e)))
	     (begin
	       (parse-input
		i (case (car e)
		    ((:top) (cddr e))
		    ((:extend) (cddr e))
		    (else `(,(car e) ,i ,@(cddr e)))))
	       (cons (car e) (cadr e)))
	     (cons :top e)))))
   (update!
    output-specs
    (map$
     (lambda (x)
       (cond
	((eval x (current-module))
	 (any-pred procedure? class? keyword?)
	 => identity)
	(else (err:output-spec x))))))
   (let*-values
       (((rexpr0) (list 'begin))
	((qexpr0) (list 'begin))
	((end?s nexts rexpr)
	 (fold-right3-with-index
	  (lambda (_ input end?s nexts rexpr)
	    (define (r end? next rexpr)
	      (values
	       (cons end? end?s)
	       (cons next nexts) rexpr))
	    (define (err) (error "Bad input spec :" input))
	    (case (car input)
	      ((:extend)
	       (cond
		((eval (cdr input) (current-module))
		 procedure? =>
		 (lambda (gen)
		   (receive (e n rexpr) (gen rexpr) (r e n rexpr))))
		(else (err))))
	      ((:bit-vector)
	       (with-gensyms
		(n r1 n1)
		(r `(cut bit-vector-null? ,n)
		   `(lambda ()
		      (receive (,r1 ,n1) (bit-vector-next ,n)
			(set! ,n ,n1)
			,r1))
		   `(let ((,n ,(cdr input))) ,rexpr))))
	      (else
	       (with-gensyms
		(end?-k next-k)
		(r end?-k next-k
		   `(,call-with-iterator ,(cdr input)
		      (lambda (,end?-k ,next-k) ,rexpr)))))))
	  '() '() rexpr0 input-specs))
	((add!s gets qexpr)
	 (let1 len (length output-specs)
	   (fold-right3-with-index
	    (lambda (idx os add!s gets qexpr)
	      (define (err) (error "Bad output spec :" os))
	      (define (r add! get nqexpr)
		(values
		 (cons
		  (if (require-component? (- len idx 1) filter?)
		    `(lambda (x) (when x (,add! x)))
		    add!)
		  add!s)
		 (cons  get  gets) nqexpr))
	      (cond
	       ((class? os)
		(with-gensyms
		 (add! get)
		 (r add! get
		    `(,call-with-builder ,os (lambda (,add! ,get) ,qexpr)))))
	       ((procedure? os)
		(receive (add! get qexpr) (os qexpr)
		  (r add! get qexpr)))
	       ((keyword? os)
		(case os
		  ((:bit-vector)
		   (let ((n 0) (idx 0))
		     (r (lambda (x)
			  (update! n (cut bit-vector-set* <> idx x))
			  (inc! idx))
			(lambda ()
			  (bit-vector-union (make-bit-vector idx) n))
			qexpr)))
		  (else (err:output-spec os))))
	       (else (err:output-spec os))))
	    '() '() qexpr0 output-specs))))
     (set-cdr! rexpr0 `(,qexpr))
     (let* ((make-args-outers '())
	    (make-args-seq
	     (apply append
		    (map-with-index
		     (lambda (i n)
		       (cond
			((require-component? i kv?)
			 `((,n) (,n)))
			((require-component? i dict)
			 (with-gensyms
			  (a b)
			  (push! make-args-outers
				 (lambda (x)
				   `(receive (,a ,b)
					(,car+cdr (,n)) ,x)))
			  `(,a ,b)))
			(else `((,n)))))
		     nexts)))
	    (args-tmp (gensyms make-args-seq))
	    (proc-rs:map (gensyms output-specs))
	    (proc-rs:fold (gensyms fold-seeds))
	    (fold-rs (gensyms fold-seeds))
	    (end-check-seq (map-list end?s))
	    (%escape? (if-gensym escape?))
	    (%index (if-gensym index?))
	    (%head? (if-gensym introspection?))
	    (misc (filter-let-lvar-spec %escape? #f %index 0 %head? #t)))
       (set-cdr!
	qexpr0
	`((until (or ,@end-check-seq ,@(insert-code* escape? %escape?))
	    (receive (,@proc-rs:map ,@proc-rs:fold)
		,(fold
		  (lambda (p e) (p e))
		  `(let ,(map-list args-tmp make-args-seq)
		     (,proc
		      ,@(insert-code* index? %index)
		      ,@(insert-code* escape? `(lambda () (set! ,%escape? #t)))
		      ,@(insert-code*
			 introspection?
			 `(begin0 ,%head? (set! ,%head? #f)))
		      ,@(insert-code* introspection? `(or ,@end-check-seq))
		      ,@args-tmp
		      ,@fold-rs))
		  make-args-outers)
	      ,(let1 xs
		   `(,@(map (pa$ list 'set!)
			    fold-rs proc-rs:fold)
		     ,@(map-list add!s proc-rs:map)
		     ,@(insert-code* index? `(inc! ,%index)))
		 (if escape?
		   `(unless ,%escape? ,@xs)
		   `(begin ,@xs)))))
	  (values ,@(map-with-index
		     (lambda (i e)
		       (if (require-component? i append?)
			 `(apply append (,e))
			 (list e)))
		     gets)
		  ,@fold-rs)))
       `(let (,@misc
	      ,@(map-list fold-rs fold-seeds))
	  ,rexpr)))))

(provide "maeve/lib/gauche/ultra-iterator")

;; Example

;; (select-module user)

;; (use util.list)
;; (use maeve.lib.gauche.macro-util)
;; (import maeve.lib.gauche.ultra-iterator)


;; (let ((ht0 (alist->hash-table
;; 	    '((i 5) (j 6) (k 7) (l 8) (m 9))
;; 	    'eqv?))
;;       (ht1 (alist->hash-table
;; 	    '((5 i) (6 j) (7 k) (8 l) (9 m))
;; 	    'eqv?)))
;;   (receive xs
;;       (macro-debug
;;        (ultra-iterator
;; 	(:introspection?-escape?-index? #t :kv? (0 2))
;; 	(<list> <vector>
;; 		(let1 n 0
;; 		  (lambda (e)
;; 		    (values (lambda (x) (inc! n x))
;; 			    (lambda () n)
;; 			    e))))
;; 	(lambda (idx esc head? tail? k0 v0 num k1 v1 ht0-val ht1-k ht1-v prev _)
;; 	  (write/ss/nl (list idx head? tail? k0 v0 num k1 
;; 			     v1 ht0-val ht1-k ht1-v))
;; 	  ;; (when (= 9 num) (esc))
;; 	  (values (and (odd?  num) (list k1 v0 k0 v1))
;; 		  (and (even? idx) num)
;; 		  idx
;; 		  `((,k0 ,k1) ,@prev)
;; 		  (odd? idx)))
;; 	('() #f)
;; 	(:top "abcdefghijklmn" :append? #t :filter? #t)
;; 	'(9 8 7 6 5 4 3 2 1 0)
;; 	'#(z y x w v u t s r q p o n m l k j i h g f e d c b a)
;; 	ht0 (:dict ht1)))
;;     (newline)
;;     (for-each write/ss/nl xs)))

;;  outputs :

;; (0 #t #f #\a #\b 9 z y)
;; (1 #f #f #\c #\d 8 x w)
;; (2 #f #f #\e #\f 7 v u)
;; (3 #f #f #\g #\h 6 t s)
;; (4 #f #f #\i #\j 5 r q)
;; (5 #f #f #\k #\l 4 p o)
;; (6 #f #t #\m #\n 3 n m)
;;
;; (z #\b #\a y v #\f #\e u r #\j #\i q n #\n #\m m)
;; #(9 #f 7 #f 5 #f 3)
;; 21
;; ((#\m n) (#\k p) (#\i r) (#\g t) (#\e v) (#\c x) (#\a z))
;; #f

;; (bit-vector-pp
;;  (macro-debug
;;   (ultra-iterator
;;    ()
;;    ((let ((n 0) (idx 0))
;;       (lambda (e)
;; 	(values
;; 	 (lambda (x)
;; 	   (update! n (cut copy-bit idx <> x))
;; 	   (inc! idx))
;; 	 (lambda ()
;; 	   (logior (expt 2 idx) n))
;; 	 e))))
;;    (lambda (i) (zero? i))
;;    ()
;;    (:extend
;;     (let1 y #b10101100111000
;;       (lambda ()
;; 	(values
;; 	 (cut = 1 y)
;; 	 (lambda ()
;; 	   (begin0
;; 	     (logand 1 y)
;; 	     (set! y (ash y -1)))))))))))


;; (define write/ss/nl (cut format/ss #t "~s\n" <>))

;; (bit-vector-pp
;;  (macro-debug
;;   (ultra-iterator
;;    ()
;;    (:bit-vector)
;;    (lambda (i) (zero? i))
;;    ()
;;    (:bit-vector (bit-vector-pp #b10101100111000)))))


;; (define (times n x) (list-ec (: i 0 n) x))

;; (define-macro (map-k k proc . xs)
;;   `(ultra-iterator () ,(times k '<list>) ,proc () ,@xs))

;; (define-macro (fold-k seeds proc . xs)
;;   `(ultra-iterator () () ,proc ,seeds ,@xs))

;; #?=(fold-k (() 0 1)
;; 	(lambda (x p0 p1 p2)
;; 	  (values (cons x p0)
;; 		  (+ x p1)
;; 		  (* x p2)))
;; 	'(1 2 3 4 5))