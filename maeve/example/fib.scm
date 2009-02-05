(define-module fib
  (import arithmetic))

(select-module fib)

(define (fib n)
  (if (< n 2)
    1
    (+ (fib (- n 2)) (fib (- n 1)))))

(define (main)
  (print-as-decimal (fib 0))
  (print-as-decimal (fib 1))
  (print-as-decimal (fib 2))
  (print-as-decimal (fib 3))
  (print-as-decimal (fib 4))
  (print-as-decimal (fib 5))
  (print-as-decimal (fib 6))
  (print-as-decimal (fib 7))
  (print-as-decimal (fib 8))
  (print-as-decimal (fib 9))
  (print-as-decimal (fib 10))
  (print-as-decimal (fib 11))
  (print-as-decimal (fib 12))
  (print-as-decimal (fib 13))
  (print-as-decimal (fib 14))
  (print-as-decimal (fib 15)))
