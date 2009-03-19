(define-module cpx
  (import immediate-type)
  (import complex-type)
  (define (print-list xs)
    (if (null? xs)
      #t
      (begin
	(print-as-decimal (car xs))
	(print-list (cdr xs)))))
  (define (vector-test:set! v i j)
    (let1 x (< i (vector-length v))
      ;; (print-as-decimal x)
      (if x
	(begin
	  ;; (print-as-decimal i)
	  (vector-set! v i j)
	  (vector-test:set! v (+ 1 i) (+ 1 j))))))
  (define (vector-test:print v i)
    (if (< i (vector-length v))
      (begin
	(print-as-decimal (vector-ref v i))
	(vector-test:print v (+ 1 i)))))
  (define (main)
    (print-list (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 '()))))))
    (let1 v1 (make-vector 9)
      (vector-test:set! v1 0 6)
      (vector-test:print v1 0)
      (print-as-decimal (vector? v1)))
    ))
