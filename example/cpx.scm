(define-module cpx
  (import core)
  (define (print-list xs)
    (if (null? xs)
      #t
      (begin
  	(print (car xs))
  	(print-list (cdr xs)))))
  (define (vector-test:set! v i j)
    (let1 x (< i (vector-length v))
      ;; (print x)
      (if x
  	(begin
  	  ;; (print i)
  	  (vector-set! v i j)
  	  (vector-test:set! v (+ 1 i) (+ 1 j))))))
  (define (vector-test:print v i)
    (if (< i (vector-length v))
      (begin
  	(print (vector-ref v i))
  	(vector-test:print v (+ 1 i)))))
  (define (main)
    (print-list (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 '()))))))
    (make-vector 9)
    (let1 v1 (make-vector 9)
      (vector-test:set! v1 0 6)
      (vector-test:print v1 0))))
