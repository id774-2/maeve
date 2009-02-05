(define-module maeve.compiler.data-flow-util
  (use srfi-1)
  ;; (use maeve.compiler.intermediate-language-util)
  ;; (use maeve.compiler.intermediate-language-instance)
  (export-all))

(select-module maeve.compiler.data-flow-util)

(define (compute-pred&succ:medium e)
  (define (hash-table-filter-push! ht k v)
    (when v (hash-table-push! ht k v)))
  (let ((pred (make-hash-table 'eqv?))
	(succ (make-hash-table 'eqv?)))
    (mir-traverse
     (target e) (type no-update)
     (use-circular-graph?)
     (handler
      (block
       (let ((s0 (block-addr:name-of* default-succ))
	     (s1 (block-addr:name-of* opt-succ)))
	 (hash-table-filter-push! succ id s0)
	 (hash-table-filter-push! succ id s1)
	 (hash-table-filter-push! pred s0 id)
	 (hash-table-filter-push! pred s1 id)))))
    (values
     (cut hash-table-get pred <> #f)
     (cut hash-table-get succ <> #f))))

(define (make-bit-vector size) (expt 2 size))

(define (bit-vector-set!  vec idx v) (copy-bit idx vec  v))
(define (bit-vector-set!   vec idx)   (copy-bit idx vec #t))
(define (bit-vector-reset! vec idx)   (copy-bit idx vec #f))

(define bit-vector-intersection logand)
(define bit-vector-union logior)
(define (bit-vector-pp x) (format #t "#,(bit-vector ~b)\n" x))

(define (bit-vector-for-each proc bit-vec)
  (until (= 1 bit-vec)
    (proc (logand 1 bit-vec))
    (set! bit-vec (ash bit-vec -1))))

(define (bit-vector-map proc bit-vec)
  (unfold (cut = 1 <>) (compose proc (cut logand 1 <>))
	  (cut ash <> -1) bit-vec))

(define (bit-vector-filter-map proc bit-vec)


(let* ((v0 (make-bit-vector 2))
       (v1 (bit-vector-union
	    v0
	    (bit-vector-set!
	     v0 0))))
  (bit-vector-pp v0)
  (bit-vector-pp v1)
  (bit-vector-for-each print v1)
  #?=(bit-vector-map identity v0))


(bit-vector-intersection #b100 #b101)



(provide "maeve/compiler/data-flow-util")