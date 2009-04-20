(use srfi-1)
(use util.match)
(use maeve.lib.gauche.pp)
(define (update-elements! proc xs)
  (pair-fold
   (lambda (xs _)
     (update! (car xs) proc)
     xs)
   #f xs)
  xs)

(use gauche.sequence)
(define-macro (debug-print x)
  (let1 results (gensym)
    `(begin
       (format/ss (current-error-port) "#?= ~s\n" ',x)
       (receive ,results ,x
	 (for-each-with-index
	  (lambda (i e)
	    (format/ss (current-error-port)
		       "#~d= ~s ~s\n" i (eq-hash e) e))
	  ,results)
	 (apply values ,results)))))

(define (normalize self)
  (let* ((outer '())
	 (result
	  (let loop ((self self))
	    (define (default-handler)
	      (if (pair? self)
		(update-elements! loop self)
		self))
	    (define (trick accs)
	      (let loop1 ((accs accs) (result #f))
		(if (null? accs)
		  result
		  (let* ((acc (car accs))
			 (tgt (acc self)))
		    (match
		     tgt
		     (('block . es)
		      (define lp (last-pair es))
		      (update!
		       (car lp)
		       (lambda (x) (set! (acc self) x) self))
		      (update! (car lp) loop)
		      (push!
		       outer
		       (lambda (extra)
			 (set! (car lp) extra)
			 tgt))
		      (loop1 (cdr accs) self))
		     (else (loop1 (cdr accs) (default-handler))))))))
	    (match
	     self
	     (('set! dist src) (trick (list caddr)))
	     (('opr2 opr v1 v2)
	      (trick (list cadddr caddr)))
	     (else (default-handler))))))
    (fold (lambda (p e) (p e)) result outer)))

(pretty-print
 (map
  normalize
  '(set! foo
	 (block
	  a b
	  (block
	   c d
	   (block
	    e f 
	    (opr2
	     +
	     (block g h i)
	     (block j k l))))))))

;;  ** syntax tree normalize problem
;; TODO : post this problem to "doukaku".

;; >||
;; (set! foo (block x y z))
;; ;; =>
;; (block x y (set! foo z))
;; ||<

;; >||
;; (opr2
;;  (block a b c)
;;  (block d e f))
;; ;; =>
;; (block
;;  a b
;;  (opr2 c (block d e f)))
;; ;; =>
;; (block
;;  a b
;;  (block
;;   d e (opr2 c f)))
;; ||<

;; >||
;; (set! foo
;;       (block
;;        x y
;;        (opr2
;; 	(block a b c)
;; 	(block d e f))))
;; ;; =>
;; (block
;;  x y
;;  (block
;;   a b
;;   (block
;;    d e (set! foo (opr2 c f)))))
;; ||<

