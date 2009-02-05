(define-module cpx
  (import arithmetic)
  (import complex-type)
  (define (print-list xs)
    (if (null? xs)
      #t
      (begin
	(print-as-decimal (car xs))
	(print-list (cdr xs)))))
  (define (vector-test:set! v i)
    (if (< (vector-length v) i)
      #t
      (begin
	;;(print-as-decimal i)
	(vector-set! v i)
	(vector-test:set! v (+ 1 i)))))
  (define (vector-test:print v i)
    (if (< (vector-length v) i)
      #t
      (begin
	(print-as-decimal (vector-ref v i))
	(vector-test:print v (+ 1 i)))))
  (define (main)
    (print-list (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 '()))))))
    
    (let1 v0 (make-vector 1)
      (vector-set! v0 0 6)
      (print-as-decimal (vector-ref v0 0)))
    
    ;;     (let1 v1 (make-vector 10)
    ;;       (print-as-decimal  (vector-length v1))
    ;;       (print-string "post make-vector")
    ;;       (vector-test:set! v1 0)
    ;;       (print-string "post vector-test:set!")
    ;;       (vector-test:print v1 0))
    ))
