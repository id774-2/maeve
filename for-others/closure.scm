;(module test (main main))

(define (sum x)
  (lambda (y)
    (let ((z (+ x y)))
      (begin
	(set! x z)
	x))))
(define (product3 x y z)
  (lambda (a)
    (let ((b (* x y z a)))
      (begin
	(set! x b)
	(set! y b)
	(set! z b)
	b))))

(define (main _)
  (let ((a (sum 111))
	(b (sum 222))
	(c (sum 333))
	(d (sum 444))
	(e (sum 555)))
    (let ((x
	   (product3
	    (e (d (c (b (a 666)))))
	    (a (b (c (d (e 777)))))
	    ((product3
	      ((sum 888) 999)
	      ((sum 1111)
	       ((sum 2222) 3333))
	      4444)
	     5555))))
      (display
       (x (x (x (x 345))))))))

(main #f)


