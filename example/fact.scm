(define-module fact
  (import core)
  (define (fact n)
    (if (zero? n)
      1
      (* n (fact (- n 1)))))
  (define (main)
    (print (fact 0))
    (print (fact 1))
    (print (fact 2))
    (print (fact 3))
    (print (fact 4))
    (print (fact 5))
    ))