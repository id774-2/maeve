
;; (define-primitive-type vector
;;   (length elements))

;; => (type_header size elements)
;; => (tag size elements)

;; (define (make-vector size) (%make-vector :size size))
;; (define (vector-length vec) (vector:size-of vec))
;; (define (vector? vec)
;;   (asm:integer= (type-tag-of vec) (const *vector-type-tag*)))
;; (define (vector-set! vec i v)
;;   ;; (sassy-form
;;   ;;  (mov eax i)
;;   ;;  (imul eax (variable-size))
;;   ;;  (add eax vec)
;;   ;;  (mov (& eax (type-introspect vector elements offset)) v))
;;   (aasm-form
   
;; ))

;; (define (make-vector size) (%make-vector :size size))
;; (define (vector-length vec) (vector:size-of vec))



;; (define (vector-ref vec i)
;;   (sassy-form
;;    (mov eax i)
;;    (imul eax (variable-size))
;;    (add eax vec)
;;    (mov eax (& eax (type-introspect vector elements offset)))))

;; (define (make-vector size)
;;   ;; allocate-vector
;;   (malloc->eax (+ size 8))

;;   ;; init-vector
;;   (mov (& eax) vector_tag)

;;   ;; optional init
;;   (mov (& eax 4) size))

(add-load-path "/home/theo/workspace/")
(use maeve.compiler.intermediate-language-util)
(use maeve.lib.gauche.complex-iterator)
(use maeve.lib.gauche.pp)

(define make-type-tag
  (let1 type-tag-counter -1
    (lambda () (inc! type-tag-counter))))

;; (define-macro (define-primitive-type name slots)
;;   (let ((slot-names slots)
;; 	(struct-size (vnum->byte (length slots)))
;; 	(type-tag (make-type-tag)))
;;     `(begin
;;        (define-macro (,(symbol-append "%make-" name) . inits)
;; 	 (let-keywords
;; 	  inits
;; 	  ,(map (cut list <> #f) slot-names)
;; 	  `(begin
;; 	     (gc-malloc ,',struct-size)
;; 	     ,@(map1-with-index
;; 		(lambda (i v) (sassy-form (mov (& eax ,i) ,v)))
;; 		slot-names))))
;;        (define-macro (,(symbol-append name "?") x)
;; 	 `(asm:integer= (type-tag-of x) ,type-tag))
;;        (begin
;; 	 ,@(map1-with-index
;; 	    (lambda (i s)
;; 	      (define-macro (,(symbol-append name ":" s "-of") x)
;; 		`(sassy-form (mov eax (& x ,(vnum->byte i))))))
;; 	    slot-names))

(define-macro (define-primitive-type name slots)
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

;; STUB
(define memory (make-vector 1000))
(define (memory-set! address v) (vector-set! memory address v))
(define (memory-ref  address)   (vector-ref  memory address))

(define gc-malloc
  (let1 counter 0
    (lambda (size)
      (begin0
	counter
	(inc! counter size)))))

(define *variable-size* 1)


(define-primitive-type vector (length elements ...))
(define-alias vector-length vector:size-of)
(define-alias vector? vector:is-a?)
(define-alias vector-ref vector:elements-of-with-index)
(define-alias vector-ref vector:elements-set!-with-index)


(define-primitive-type pair (car cdr))
(define-alias-as-macro set-car! cons:car-set!)
(define-alias-as-macro set-cdr! cons:cdr-set!)
(define-alias car cons:car-of)
(define-alias cdr cons:cdr-of)
(define-alias pair? cons:is-a?)

(define (cons a d)
  (let1 r (pair:allocate-instance)
    (cons:car-set! r a)
    (cons:cdr-set! r a)
    r))

(define (make-vector size init)
  (let ((vec (vector:allocate-instance size)))
    (vector:size-set! vec size)
    (let loop (i size) (vector-set! vec i init))
    vec))
(let* ((size 100)
       (vec (vector:allocate-instance size)))
  (vector:length-set! vec size)
  (for-each-with-index
   (lambda (i x) (vector:elements-set!-with-index vec i x))
   '(a b c d e f g h i))
  vec)
