(define-module maeve.compiler.misc
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (export-all))

(select-module maeve.compiler.misc)

(define (compute-env-overwrite
	 dists srcs make-key make-mov make-tmp copy-tmp key=? key>=?)
  (let* ((find-key-dist (lambda (x xs) (find (cut key>=? x <>) xs)))
	 (find-key-src  (lambda (x xs)
			  (find (any-pred
				 (compose not (cut key>=? x <>))
				 (cut key=? x <>))
				xs)))
	 (trm (make-tree-map key=? key>=?)) (nneg 0) (npos 0)
	 (src-keys  (map make-key srcs))
	 (dist-keys (map make-key dists)))
    (for-each-with-index
     (lambda (i dk)
       (when (find-key-dist dk src-keys)
	 (tree-map-put! trm dk i)))
     dist-keys)
    (for-each-with-index
     (lambda (si sk)
       (and-let* ((dk (find-key-src sk dist-keys)))
	 (tree-map-update!
	  trm dk
	  (lambda (di)
	    (rlet1 r (- si di)
		   (cond
		    ((negative? r) (inc! nneg))
		    ((positive? r) (inc! npos)))))
	  0)))
     src-keys)
    (let-values
	(((pred default)
	  (if (> nneg npos)
	    (values (cut <= 0 <>) -1)
	    (values (cut >= 0 <>) 1)))
	 ((broken) '()) ((s1) '()) ((s2) '()) ((s3) '()))
      (for-each
       (lambda (d dk s sk)
	 (when (find-key-src sk broken)
	   (error "compute-env-overwrite : fuck-up! : " srcs dists))
	 (cond
	  ((pred (tree-map-get trm dk default))
	   (push! s2 (make-mov d s))
	   (push! broken dk))
	  (else
	   (let1 tmp (make-tmp)
	     (push! s1 (make-mov tmp s))
	     (push! s3 (make-mov d (copy-tmp tmp)))))))
       dists dist-keys srcs src-keys)
      (append (reverse! s1) (reverse! s2) (reverse! s3)))))

(define (%make-set!-sequence make-set! make-tmp dists srcs)
  (compute-env-overwrite
   dists srcs
   (rec
    (loop x)
    (cond
     ((mem? x) (list 'mem (mem:offset-of x) (loop (mem:base-of x))))
     ((register? x) (list 'register (register:num-of x)))
     ((result? x) (list 'result (result:num-of x)))
     ((svar? x) (list 'svar (svar:type-of x)))
     ((const? x) (list 'const (const:v-of x)))
     (else (il:id x))))
   make-set! make-tmp identity equal? (cut list>=? equal? <> <>)))

;; #?=(compute-env-overwrite
;;     '((r 0) (r 1) (r 2))
;;     '((r 1) (r 2) (r 0))
;;     identity list (lambda () '(tmp)) identity 'equal?)

;; #?=(compute-env-overwrite
;;     '((r 1) (r 2))
;;     '((r 0) (mem (r 1)))
;;     identity list (let1 n -1 (lambda () (symbol-append 'tmp- (inc! n))))
;;     identity equal? (cut list>=? equal? <> <>))
;; ;; => ((tmp-0 (mem (r 1))) ((r 1) (r 0)) ((r 2) tmp-0))

(provide "maeve/compiler/misc")