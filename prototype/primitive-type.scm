(define-module maeve.compiler.primitive-type
  (use maeve.compiler.intermediate-language-util))

(select-module maeve.compiler.primitive-type)

(define make-type-tag
  (let1 type-tag-counter -1
    (lambda () (inc! type-tag-counter))))

(define-macro (define-primitive-type name slots . options)
  (receive (slots rest-slot)
      (let1 r (reverse slots)
	(if (eq? (car r) '...)
	  (values (reverse (cdr r)) (cadr r))
	  (values slots #f)))
    (let ((default-size
	    ;; (type-tag slot1 slot2 ...)
	    (+ 1
	       (if rest-slot
		 (- #0=(length slots) 1)
		 #0#)))
	  (type-tag (make-type-tag)))
      `(begin
	 (define-macro (,(symbol-append name ":allocate-instance")
			,@(insert-code* rest-slot 'rest-size))
	   `(let1 r (gc-malloc ,,(if rest-slot
				   ``(+ (* *variable-size* ,',default-size)
					,rest-size)
				   ``(* *variable-size* ,',default-size)))
	      (memory-set! r ,',type-tag)
	      r))
	 (define-macro (,(symbol-append name ":is-a?") x)
	   `(let1 tag (memory-ref ,x)
	      (eq? ,tag ,',type-tag)))
	 ,@(append-map1-with-index
	    (lambda (i slot-name)
	      `((define-macro (,(symbol-append name ":" slot-name "-set!")
			       dist src)
		  `(memory-set! (+ ,dist (* ',',i *variable-size*)) ,src))
		(define-macro (,(symbol-append name ":" slot-name "-of")
			       x)
		  `(memory-ref (+ ,x (* ',',i *variable-size*))))
		,@(insert-code
		   (eq? slot-name rest-slot)
		   `((define-macro (,(symbol-append
				      name ":" slot-name "-of-with-index")
				    x index)
		       `(memory-ref
			 (+ ,x (* (+ ',',i ,index) *variable-size*))))
		     (define-macro (,(symbol-append
				      name ":" slot-name "-set!-with-index")
				    x index v)
		       `(memory-set!
			 (+ ,x (* (+ ',',i ,index) *variable-size*))
			 ,v))))))
	    slots)))))

;; ;; STUB
;; (define memory (make-vector 1000))
;; (define (memory-set! address v) (vector-set! memory address v))
;; (define (memory-ref  address)   (vector-ref  memory address))

;; (define gc-malloc
;;   (let1 counter 0
;;     (lambda (size)
;;       (begin0
;; 	counter
;; 	(inc! counter size)))))

;; (define *variable-size* 1)

(define-primitive-type vector (length elements ...))
(define (vector-length x)   (vector:length-of x))
(define (vector? x)         (vector:is-a? x))
(define (vector-ref x i)    (vector:elements-of-with-index x i))
(define (vector-set! x i v) (vector:elements-set!-with-index x i v))

(define-primitive-type pair (car cdr))
(define (set-car! x y) `(cons:car-set! ,x ,y))
(define (set-cdr! x y) `(cons:cdr-set! ,x ,y))
(define car   cons:car-of)
(define cdr   cons:cdr-of)
(define pair? cons:is-a?)



;; (define (cons a d)
;;   (let1 r (pair:allocate-instance)
;;     (cons:car-set! r a)
;;     (cons:cdr-set! r a)
;;     r))

;; (define (make-vector size init)
;;   (let ((vec (vector:allocate-instance size)))
;;     (vector:size-set! vec size)
;;     (let loop (i size) (vector-set! vec i init))
;;     vec))

;; (let* ((size 100)
;;        (vec (vector:allocate-instance size)))
;;   (vector:length-set! vec size)
;;   (for-each-with-index
;;    (lambda (i x) (vector:elements-set!-with-index vec i x))
;;    '(a b c d e f g h i))
;;   vec)

(provide "maeve/compiler/primitive-type")
