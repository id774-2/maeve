(define-module maeve.lib.gauche.values
  (use maeve.lib.gauche.complex-iterator)
  (export-all))

(select-module maeve.lib.gauche.values)

(define-macro (values-filter1 expr . spec)
  (let1 vs (map (lambda (_) (gensym)) spec)
    `(receive ,vs ,expr
       (values
	,@(map
	   (lambda (v s)
	     (if s
	       `(,s ,v)
	       v))
	   vs spec)))))

(define-macro (values-filter1-values expr . spec)
  (let1 vs (map (lambda (_) (gensym)) spec)
    `(receive ,vs ,expr
       (apply
	values
	(append
	 ,@(map
	    (lambda (v s)
	      (if s
		`(call-with-values (lambda () (,s ,v))
		   (lambda x x))
		`(list ,v)))
	    vs spec))))))

(define-macro (values-filter* expr . spec)
  (let1 vs (map
	    (lambda _
	      (map (lambda _ (gensym)) spec))
	    expr)
    (fold-right
     (lambda (vs expr prev)
       `(receive ,vs ,expr ,prev))
     `(values
       ,@(map
	  (lambda (vs s) (if s `(,s ,@vs) `(list ,@vs)))
	  (map1-with-index
	   (lambda (i _)
	     (map (cut list-ref <> i) vs))
	   spec)
	  spec))
     vs expr)))

(define-macro (let-values specs expr . more)
  (fold-right
   (lambda (e body)
     `(receive ,(car e)
	  ,(cadr e)
	,body))
   (if (null? more)
     expr
     `(begin ,expr ,@more))
   specs))

(define-macro (let*-values specs expr . more)
  `(let-values ,specs ,expr ,@more))

(define-macro (let-values/init-sequence-bind in-init-varspec varspecs . expr)
  (receive (iivs:pre iivs:post)
      (map2
       (lambda (s)
	 (receive (pre post)
	     (if (pair? (car s))
	       (let1 true-var (map (lambda _ (gensym)) (car s))
		 (values true-var `(,(car s) (values ,@true-var))))
	       (let1 true-var (gensym)
		 (values true-var `((,(car s)) ,true-var))))
	   (values
	    (list pre (cadr s))
	    post)))
       in-init-varspec)
    (let1 body
	(fold-right
	 (lambda (e body)
	   `(receive ,(car e) (let-values/init-sequence-bind () ,iivs:post ,(cadr e))
	      ,body))
	 `(begin ,@expr)
	 varspecs)
      (if (null? iivs:pre)
	body
	`(let-values/init-sequence-bind () ,iivs:pre ,body)))))

(define-macro (let-values/init-sequence-bind* x y z)
  `(let-values/init-sequence-bind ,x ,y ,z))

;; ;; Example

;; (let-values/init-sequence-bind
;;  (((x y z) (values 100 200 300))
;;   (ijk (values 3 4 5)))
;;  (((a b) (values (+ x 1) (+ y 2)))
;;   ((c d e) (values (+ y 3) (+ z 4) ijk)))
;;  (list* a b c d e))

;; ;; => (101 202 203 304 3 4 5)

(provide "maeve/lib.gauche/values")
