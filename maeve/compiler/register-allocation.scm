(define-module maeve.compiler.register-allocation
  (use gauche.array)
  (use util.combinations)
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (use maeve.compiler.data-flow-analysis)
  (export-all))

(select-module maeve.compiler.register-allocation)

(define *sp* (make-svar :type 'sp))
(define *fp* (make-svar :type 'fp))

(define-values (ref-stack-by-sp/const ref-stack-by-fp/const)
  (let1 gen
      (lambda (base offset)
	(unless (integer? offset) (error "mem offset must be ingeter :" offset))
	(make-mem :base base :offset (* (variable-size) offset)))
    (values (cut gen *sp* <>) (cut gen *fp* <>))))

(define (proc-parameter-allocation:stack type xs)
  (let* ((n 0)
	 (ys
	  (map1-with-index
	   (lambda (i _)
	     (inc! n)
	     (case type
	       ((lmd)  (ref-stack-by-fp/const i))
	       ((call) (ref-stack-by-sp/const i))
	       (else (error "invalid procparam type :" type))))
	   xs)))
    (values ys (* (variable-size) n))))

(define (proc-parameter-allocation:register type xs)
  (let* ((%num-of-regs (num-of-registers))
	 (n 0)
	 (ys
	  (map1-with-index
	   (lambda (i _)
	     (if (> %num-of-regs i)
	       (case type
		 ((lmd call) (make-register :num i))
		 (else (error "invalid procparam type :" type)))
	       (begin
		 (inc! n)
		 (case type
		   ((lmd)  (ref-stack-by-fp/const i))
		   ((call) (ref-stack-by-sp/const i))
		   (else (error "invalid procparam type :" type))))))
	   xs)))
    (values ys (* (variable-size) n))))

(define (register-allocation:stack paramalloca e)
  (let ((lva-table (make-hash-table 'eq?))
	(cur-table (make-hash-table 'eq?)))
    (define cur-default (cut make-vector (num-of-registers) #f))
    (mir-traverse
     (target e)
     (type no-update)
     (handler
      (lmd
       (let-values (((cur) (cur-default))
		    ((dists arg-size) (paramalloca 'lmd param)))
	 (for-each
	  (lambda (lv e)
	    (hash-table-put! lva-table lv e)
	    (when (register? e) (vector-set! cur (register:num-of e) #t)))
	  param dists)
	 (when-debug:regalloca
	  (format #t "cur ~s : ~s ~s ~s\n"
		  id (filter-map register:num-of* dists) cur (eq-hash cur)))
	 (hash-table-put! cur-table *self* cur)
	 (for-each-with-index
	  (lambda (i lv)
	    (hash-table-put!
	     lva-table lv (ref-stack-by-fp/const (- (+ 1 i)))))
	  local-vars)))))
    (when-debug:regalloca (hash-table-dump lva-table))
    (make-register-allocation-result
     :compute-using-register
     (lambda (xs) (hash-table-get* cur-table (find lmd? xs) (cur-default)))
     :lvar-allocation (lambda (_ lv) (hash-table-get lva-table lv)))))

(define (pp-dim2-array dim1 dim2 a)
  (define (dim2-array? a)
    (let1 s (array-shape a)
      (= 2 (array-length s 0) (array-length s 1))))
  (unless (dim2-array? a)
    (error "Dimension of array is not 2. That's shape :" (shape a)))
  (let ((start1 (array-start a 0))
	(start2 (array-start a 1))
	(cmax 0))
    (define (%update x)
      (cond
       ((string-length (write-to-string x))
	(cut < cmax <>)
	=> (lambda (l) (set! cmax l)))))
    (vector-for-each (lambda (_ e) (%update e)) dim1)
    (vector-for-each (lambda (_ e) (%update e)) dim2)
    (array-for-each-index
     a
     (lambda (i j) (%update (array-ref a i j))))
    (let1 out (cut format #t #`"~,|cmax|@a " <>)
      (array-for-each-index
       a
       (lambda (i j)
	 (when (= start2 j)
	   (when (= start1 i)
	     (out "")
	     (vector-for-each
	      (lambda (_ e) (out e))
	      dim2))
	   (newline)
	   (out (vector-ref dim1 (- i start1))))
	 (let1 x (array-ref a i j)
	   (out (if x x "")))))))
  (newline))

(define (matrix-size matrix)
  (let ((e1 (array-end matrix 1))
	(e2 (array-end matrix 1)))
    (if (= e1 e2) e1
	(error "interference matrix required, but got :" matrix))))

(define (matrix->graphviz i->v matrix)
  (print "digraph cfg {")
  (print "  node [shape = \"plaintext\", fontsize = \"10\"];")
  (dotimes (i (matrix-size matrix))
    (format #t "  ~a [label = \"~a ~a\"];\n" i i (i->v i)))
  (format #t "  edge [dir = none]\n\n")
  (array-for-each-index
   matrix
   (lambda (i j)
     (when (and (array-ref matrix i j)
		(< i j))
       (format #t "  ~s -> ~s;\n" i j))))
  (print "}"))

(define (register-allocation:primitive-approximation paramalloca e)
  (define lva-table (make-hash-table 'eq?))
  (define cur-table (make-hash-table 'eq?))
  (define cur-default (cut make-vector (num-of-registers) #f))
  (define (make-interference-graph slive)
    (define (%make-interference-graph live-rights)
      (let* ((vars
	      (sort
	       (fold (lambda (e p) (lset-union eqv? e p))
		     '() live-rights)
	       il<?))
	     (vlen (length vars))
	     (v->i (alist->hash-table (map1-with-index xcons vars) 'eqv?))
	     (matrix (make-array (shape 0 vlen 0 vlen) #f))
	     (index (vector 0 0)))
	(for-each
	 (lambda (inf)
	   (combinations-for-each
	    (lambda (x)
	      (let ((ai (hash-table-get v->i (car x)))
		    (bi (hash-table-get v->i (cadr x))))
		(array-set! matrix ai bi #t)
		(array-set! matrix bi ai #t)))
	    inf 2))
	 live-rights)
	(values
	 matrix
	 (cut hash-table-get v->i <> #f)
	 (let1 i->v (alist->hash-table (map1-with-index cons vars) 'eqv?)
	   (cut hash-table-get i->v <> #f))
	 (let1 x (list->vector (map il:id vars))
	   (cut pp-dim2-array x x matrix)))))
    (%make-interference-graph
     (hash-table-map slive (compose (map$ live-elm:var-of) second-value))))
  (mir-traverse
   (target e) (type no-update)
   (handler
    (lmd
     (when-debug:regalloca
      (format #t " ** register-allocation ~s\n" id))
     (let*-values
	 (((%slive) (live *self*))
	  (_ (when-debug:regalloca
	      (hash-table-dump*
	       %slive :pre-key-filter il:id :value-filter
	       (map$ (lambda (x)
		       (if (live-elm:end?-of x)
			 (list (live-elm:var-of x) (live-elm:end?-of x))
			 (live-elm:var-of x)))))))
	  ((matrix v->i i->v p) (make-interference-graph %slive))
	  ((dists arg-size) (paramalloca 'lmd param))
	  ((msize) (matrix-size matrix))
	  ((kill-table) (make-vector msize #f))
	  ((index-sum) 0)
	  ((%num-of-regs) (num-of-registers))
	  ((stack) '())
	  ((result) (make-vector msize #f))
	  ((registers) (list-ec (: i 0 %num-of-regs) i)))
       (define (degree vindex)
	 (let ((c 0) (edge-to '()))
	   (dotimes (i msize)
	     (when (array-ref matrix vindex i)
	       (push! edge-to i)
	       (unless (kill? i) (inc! c))))
	   (values c edge-to)))
       (define kill? (cut vector-ref kill-table <>))
       (define (kill vindex)
	 (vector-set! kill-table vindex #t)
	 ;; 	(dotimes (i msize)
	 ;; 	  (array-set! matrix vindex i #f)
	 ;; 	  (array-set! matrix i vindex #f))
	 (inc! index-sum))
       (when-debug:regalloca (print " ** interference matrix") (p))
       (for-each
	(lambda (lv e)
	  (hash-table-put! lva-table lv e)
	  (cond ((v->i lv)
		 => (lambda (i)
		      (kill i)
		      (vector-set! result i (or (register:num-of* e) e))))))
	param dists)
       (until (= index-sum msize)
	 (push!
	  stack
	  (rlet*-last
	   ((i 0) (r #f))
	   (while (and (> msize i)
		       (or
			(kill? i)
			(cond ((degree i)
			       (lambda (deg _) (> %num-of-regs deg))
			       => (lambda (deg edge-to)
				    (set! r (cons i edge-to))
				    #f))
			      (else #t))))
	     (inc! i))
	   (if r
	     (kill (car r))
	     (error "unsupport spill.")))))
       (for-each
	(lambda (vs)
	  (unless (vector-ref result (car vs))
	    (vector-set!
	     result (car vs)
	     (car
	      (lset-difference
	       = registers
	       (filter-map1
		(lambda (x)
		  (cond
		   ((vector-ref result x) integer? => identity)
		   (else #f)))
		(cdr vs)))))))
	stack)
       (when-debug:regalloca
	(format #t "slv-result ~s : ~s ~s\n" id result stack))
       (let1 cur (cur-default)
	 (vector-for-each
	  (lambda (i e)
	    (when (integer? e)
	      (vector-set! cur e #t)
	      (hash-table-put! lva-table (i->v i) (make-register :num e))))
	  result)
	 (hash-table-put! cur-table *self* cur))
       (hash-table-update-all!
	%slive
	(lambda (k elms _)
	  (rlet1
	   cur (cur-default)
	   (for-each
	    (lambda (v)
	      (and-let* ((x (vector-ref result (v->i (live-elm:var-of v))))
			 (_ (integer? x)))
		(if (live-elm:end?-of v)
		  (vector-set! cur x 'end)
		  (vector-set! cur x #t))))
	    elms)
	   (when-debug:regalloca
	    (format #t "cur ~s : ~s ~s ~s\n"
		    (il:id k)
		    (map
		     (lambda (v)
		       (vector-ref result (v->i (live-elm:var-of v))))
		     elms)
		    cur (eq-hash cur)))))
	:dist cur-table)))))
  
  ;;(with-output-to-file "./interference-graph.dot"
  ;; (cut matrix->graphviz i->v m))
;;   (hash-table-dump* lva-table :pre-key-filter il:id)
;;   (hash-table-dump* cur-table :pre-key-filter il:id
;; 		    :value-filter (lambda (v) (cons (eq-hash v) v)))
  (make-register-allocation-result
   :lvar-allocation (lambda (_ lv) (hash-table-get lva-table lv))
   :compute-using-register
   (lambda (xs)
     (cond
      ((find-and-value
	(lambda (x) (hash-table-get cur-table x #f))
	xs) => identity)
      (else (error "compute-using-register not found :" xs))))))

;; (receive (%make-set! %make-set!-vls %make-opr2)
;;     (let1 lv (make-hash-table 'eq?)
;;       (define (make-one x)
;; 	(case/pred
;; 	 x
;; 	 (symbol?
;; 	  (cond
;; 	   ((hash-table-get lv x #f) => identity)
;; 	   (else (rlet1 r (make-lvar :name x) (hash-table-put! lv x r)))))
;; 	 (il? x)
;; 	 (else (make-const :v x))))
;;       (values
;;        (lambda (d s)
;; 	 (make-set! :dist (make-one d) :src (make-one s)))
;;        (lambda (ds s)
;; 	 (make-set!-vls :dists (map make-one ds) :src (make-one s)))
;;        (lambda (op v1 v2)
;; 	 (make-opr2 :opr op :v1 (make-one v1) :v2 (make-one v2)))))
;;   (let* ((b6 (%make-block '()))
;; 	 (b5 (%make-block
;; 	      (%make-set! 'i 2)
;; 	      b6))
;; 	 (b4 (%make-block
;; 	      (%make-set! 'j (%make-opr2 '/ 'i 2))
;; 	      b5))
;; 	 (b3 (%make-block
;; 	      (list
;; 	       (%make-set! 'j (%make-opr2 '- 'j 1))
;; 	       (%make-set!-vls (list 'k 'l) 30))
;; 	      b4))
;; 	 (b2 (%make-block
;; 	      (%make-set!-vls
;; 	       (list 'i 'k)
;; 	       (make-vls :es (list (%make-opr2 '+ 'i 1)
;; 				   (%make-opr2 '- 'j 'i))))
;; 	      b3))
;; 	 (b1 (%make-block
;; 	      (list
;; 	       (%make-set! 'j 10)
;; 	       (%make-set! 'i -8))
;; 	      b2)))
;;     (%block:opt-succ-set!
;;      b3 b2 (%make-opr2 '!= 'j 0))
;;     (%block:opt-succ-set!
;;      b4 b6 (%make-opr2 '< 'i 8))
;;     (%block:default-succ-set! b6 b2)
;;     (let1 x (make-seq :es (list b1 b2 b3 b4 b5 b6))
;;       (print " ** reach")
;;       (hash-table-dump*
;;        (reach x)
;;        :pre-key-filter il:id
;;        :value-filter
;;        (lambda (x)
;; 	 (hash-table-map
;; 	  x (lambda (k vs)
;; 	      (cons
;; 	       (lvar:name-of* k)
;; 	       (map
;; 		(lambda (v) (list (il:id (rd-elm:src-of v)) (rd-elm:num-of v)))
;; 		vs))))))
;;       (print " ** live")
;;       (hash-table-dump*
;;        (live x)
;;        :pre-key-filter il:id
;;        :value-filter (map$ lvar:name-of*))
;;       (il->graphviz* "nak" x)
;;       (process-wait-any #t))))

(provide "maeve/compiler/register-allocation")