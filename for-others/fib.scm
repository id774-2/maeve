(module test (main main))

(define (fib n)
  (if (< n 2)
    1
    (+ (fib (- n 2)) (fib (- n 1)))))

(define (main _)
  (write (fib 39)))