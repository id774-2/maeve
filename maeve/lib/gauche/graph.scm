(define-module maeve.lib.gauche.graph
  (use util.match)
  (use srfi-1)
  (use gauche.collection)
  (use maeve.lib.gauche.misc)
  (use maeve.lib.gauche.list-util)
  (use maeve.lib.gauche.macro-util)
  (export-all))

(select-module maeve.lib.gauche.graph)

;; directed edge (u,v) is represented following :
;;   an entry of hash-table :
;;     u -> (attr-of-vertex-u (v . attr-of-edge-u->v) . other-edges)


;; directed weighted graph that is matrix 0
;; is represented data structure 1 that we can make by code 2.

;; matrix 0 :
;;   a b c
;; a 0 3 8
;; b 0 0 0
;; c 5 0 0
;;   and vertex weight : (a -1) (b -2) (c -3)

;; data structure 1 :
;; hash-table :
;;   b -> (-2)
;;   c -> (-3 (b . 5))
;;   a -> (-1 (c . 8) (b . 3))

;; code 2 :
;; (let1 g (make-ht-graph
;; 	 :make-edge (lambda (u v x) x)
;; 	 :make-vertex (lambda (u x) x))
;;   (add-edge! g 'a 'b
;; 	     :e-attr '(3)   ;; mean weight of edge (a,b)
;; 	     :v0-attr '(-1) ;; mean weight of vertex a
;; 	     :v1-attr '(-2) ;; mean weight of vertex b
;; 	     )
;;   (add-edge! g 'a 'c :e-attr '(8) :v1-attr '(-3))
;;   (add-edge! g 'c 'b :e-attr '(5))
;;   (dump-graph g))

(define-class <graph> ()
  ((edge=? :init-keyword :edge=? :accessor edge=?-of :init-value eqv?)
   (undirected? :init-keyword :undirected? :accessor undirected-graph?
		:init-value #f)
   (table :init-keyword :table :accessor table-of)))

(define directed-graph? (compose not undirected-graph?))

(define-class <ht-graph> (<graph>)
  ((make-edge :init-keyword :make-edge :accessor make-edge-of
	      :init-value (lambda _ #f))
   (edge-observer:add
    :init-keyword :edge-observer:add :accessor edge-observer:add-of
    :init-value #f)
   (edge-observer:delete
    :init-keyword :edge-observer:delete :accessor edge-observer:delete-of
    :init-value #f)
   (make-vertex :init-keyword :make-vertex :accessor make-vertex-of
		:init-value (lambda _ #f))))

(define (make-ht-graph . rest)
  (let-keywords
   rest ((ht-type 'eqv?) . rest)
   (apply make <ht-graph> :table (make-hash-table ht-type) rest)))

(define-method vertex-null? ((g <ht-graph>))
  (with-iterator ((table-of g) end? _)
    (end?)))

(define-method edge-null? ((g <ht-graph>))
  (not (select-edge g)))

(define-method select-edge ((g <ht-graph>))
  (with-iterator ((table-of g) end? next)
    (let loop ()
      (cond
       ((end?) #f)
       ((next)
	(compose pair? cdr) =>
	(lambda (x)
	  (match-let1 (u uattr (v . e-attr) . _) x
		      (vector u v e-attr))))
       (else (loop))))))

(define-method get-vertex-attr ((g <ht-graph>) k . opt-fall-back)
  (car
   (hash-table-get*
    (table-of g) k
    (if (null? opt-fall-back)
      (errorf "vertex ~s does not exist in graph ~s." k g)
      (car opt-fall-back)))))

(define-method add-vertex! ((g <ht-graph>) v . rest)
  (let-keywords
   rest ((v-if-exists #f) (v-attr '()))
   (rlet*-car
    ((result (undefined)) (ht (table-of g)))
    (define (put! edges)
      (hash-table-put! ht v (cons (apply (make-vertex-of g) v v-attr) edges)))
    (cond
     ((hash-table-get ht v #f)
      => (lambda (a/e)
	   (case v-if-exists
	     ((:clear) (put! '()))
	     ((:overwrite) (put! (cdr a/e)))
	     ((:error) (errorf "vertex ~s already exists in ~s." v g))
	     ((#f) (set! result #f))
	     (else (error ":clear, :overwrite, :error or #f expected for :v-if-exists, but got" e-if-exists)))))
     (else (put! '()))))))

(define-method add-edge! ((g <ht-graph>) s e . rest)
  (let-keywords
   rest ((e-if-exists :overwrite) (e-attr '())
	 (v0-if-exists #f) (v1-if-exists #f)
	 (v0-attr '()) (v1-attr '()))
   (define (%add-edge! s e)
     (let* ((ht (table-of g)) (result (undefined)) (eq (edge=?-of g))
	    (%e (apply (make-edge-of g) s e e-attr)) (edge (cons e %e)))
       (add-vertex! g s :v-if-exists v0-if-exists :v-attr v0-attr)
       (add-vertex! g e :v-if-exists v1-if-exists :v-attr v1-attr)
       (cond ((edge-observer:add-of g) procedure? => (cut <> s e %e)))
       (hash-table-update!
	ht s
	(match-lambda
	 ((v-attr . edges)
	  (cons
	   v-attr
	   (case e-if-exists
	     ((:append) (cons edge edges))
	     ((:overwrite) (lset-adjoin eq edges edge))
	     (else
	      (if (find (cut eq edge <>) edges)
		(case e-if-exists
		  ((:error)
		   (errorf "edge ~s -> ~s already exists in ~s." s e g))
		  ((#f) (set! result #f) edges)
		  (else (error ":overwrite, :append, :error or #f expected for :e-if-exists, but got" e-if-exists)))
		(cons edge edges)))))))
	result)))
   (%add-edge! s e)
   (when (undirected-graph? g) (%add-edge! e s))))

(define (%delete-edge! g s e p)
  (let1 xs (hash-table-get (table-of g) s)
    (let1 eq (edge=?-of g)
      (update! (cdr xs)
	       (remove$
		(lambda (x)
		  (and (eq e (car x))
		       (begin (if (procedure? p) (p s e (cdr x)))
			      #t))))))))

(define-method delete-edge! ((g <ht-graph>) s e)
  (let1 p (edge-observer:add-of g)
    (%delete-edge! g s e p)
    (when (undirected-graph? g) (%delete-edge! g e s p))))

(define-method delete-vertex! ((g <ht-graph>) v)
  (when (hash-table-delete! (table-of g) v)
    (hash-table-for-each
     (table-of g)
     (lambda (s _) (%delete-edge! g s v #f)))))

(define-method find-edge-and-value (pred (g <ht-graph>))
  (with-iterator ((table-of g) end? next)
    (let ((extra-end? #f) (r #f))
      (while (and (not (end?)) (not extra-end?) (next))
	pair? => x
	(cond
	 ((let1 s (car x)
	    (find-and-value
	     (lambda (e) (pred s (car e) (cdr e)))
	     (cddr x)))
	  second-value =>
	  (lambda (x _)
	    (set! extra-end? #t)
	    (set! r x)))))
      r)))

(define-method filter-map-edges (pred (g <ht-graph>))
  (rlet1 result '()
	 (with-iterator ((table-of g) end? next)
	   (while (and (not (end?)) (next))
	     pair? => x
	     (let1 s (car x)
	       (for-each
		(lambda (e)
		  (and-let* ((x (pred s (car e) (cdr e))))
		    (push! result x)))
		(cddr x)))))))

(define-method for-each-edges (proc (g <ht-graph>))
  (hash-table-for-each
   (table-of g)
   (lambda (s a/e)
     (for-each
      (lambda (e) (pred s (car e) (cdr e)))
      (cdr a/e)))))

(define-method for-each-vertex (proc (g <ht-graph>))
  (hash-table-for-each
   (table-of g)
   (lambda (s a/e) (proc s (car a/e)))))

(define-method map-vertex (proc (g <ht-graph>))
  (hash-table-map
   (table-of g)
   (lambda (s a/e) (proc s (car a/e)))))
     
(define graph-edges (cut filter-map-edges vector <>))

(define-method dump-graph ((g <ht-graph>))
  (hash-table-for-each
   (table-of g)
   (lambda (k v) (format #t "~s ~s\n" k v))))

(provide "maeve/lib/gauche/graph")

;; ;; Example

;; (select-module user)

;; (use srfi-1)
;; (use util.match)
;; (import maeve.lib.gauche.graph)

;; (let1 g (make-ht-graph
;; 	 :make-edge (lambda (u v x) x)
;; 	 :make-vertex (lambda (u x) x))
;;   (add-edge! g 'a 'b
;; 	     :e-attr '(3)   ;; mean weight of edge (a,b)
;; 	     :v0-attr '(-1) ;; mean weight of vertex a
;; 	     :v1-attr '(-2) ;; mean weight of vertex b
;; 	     )
;;   (add-edge! g 'a 'c :e-attr '(8) :v1-attr '(-3))
;;   (add-edge! g 'c 'b :e-attr '(5))
;;   (dump-graph g))

;; (let1 g (make-ht-graph :make-edge vector :undirected? #t)
;;   #?=(for-each
;;    (lambda (x) (add-edge! g (car x) (cadr x)))
;;    '((a b) (b c) (c e) (c d) (d e) (d f) (d g) (d h) (e f) (h g)
;;      (x a) (x b) (x c) (x d)))
  
;;   #?=(delete-vertex! g 'x)
  
;;   #?=(filter-map-edges
;;       (lambda (x y _) (and (eq? y 'e) (list x y)))
;;       g)

;;   (dump-graph g)

;;   (let ((cover '()) (matching '()))
;;     (while (select-edge g) identity => x
;;       (match-let1
;;        #(u v _) x
;;        (update! cover (cut lset-adjoin eqv? <> u v))
;;        (update! matching (cut lset-adjoin equal? <> (list u v)))
;;        (delete-vertex! g u)
;;        (delete-vertex! g v)))
;;     #?=matching
;;     #?=cover))
