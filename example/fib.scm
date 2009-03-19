(define-module fib
  (import immediate-type))

(select-module fib)

(define (fib n)
  (if (< n 2)
    1
    (+ (fib (- n 2)) (fib (- n 1)))))

(define (main)
  (print (fib 0))
  (print (fib 1))
  (print (fib 2))
  (print (fib 3))
  (print (fib 4))
  (print (fib 5))
  (print (fib 6))
  (print (fib 7))
  (print (fib 8))
  (print (fib 9))
  (print (fib 10))
  (print (fib 11))
  (print (fib 12))
  (print (fib 13))
  (print (fib 14))
  (print (fib 15)))
