(define-module fact
  (import arithmetic)
  (define (fact n)
    (if (zero? n)
      1
      (* n (fact (- n 1)))))
  (define (main)
;;     (print-as-decimal (fact 0))
;;     (print-as-decimal (fact 1))
    (print-as-decimal (fact 2))
    (print-as-decimal (fact 3))
    (print-as-decimal (fact 4))
    (print-as-decimal (fact 5))
    ))