(define-module closure
  (import core)
  (define (main)
    ((lambda (a b c)
       ((lambda (x y z)
	  (print a)
	  (print b)
	  (print c))
	44444 55555 66666))
     11111 22222 33333)))