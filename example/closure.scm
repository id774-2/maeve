(define-module closure
  (define (main)
    ((lambda (a b c)
       ((lambda (i j k)
	  ((lambda (x y z)
	     (values a b c i j k x y z)
	     ;;(print a)(print b)(print c)
	     ;;(print i)(print j)(print k)
	     ;;(print x)(print y)(print z)
	     )
	   6 7 8))
	3 4 5))
     0 1 2)))