(debug-print-width 100000)

(use util.match)

(define (%%macroexpand tree)
  (let1 mod (make-module #f)
    (let loop ((x tree))
      (match
       x
       (((or 'define-macro 'define) (name . args) es ...)
	(eval `(,(car x) ,name (lambda ,args ,@es)) mod)
	x)
       (((or 'define-macro 'define) _ _) (eval x mod) x)
       (else
	(if (pair? x)
	  (let1 r (eval `(macroexpand ',x) mod)
	    (if (equal? x r)
	      (map loop r)
	      (loop r)))
	  x))))))

#?=(%%macroexpand
    '(begin
       (define-macro (f x) `(value ,x))
       (define-macro (g x) `(x (f ,x)))
       (define h g)
       (g 30)))

;; =>
;; (begin
;;   (define-macro (f x) `(value ,x))
;;   (define-macro (g x) `(x (f ,x)))
;;   (define h g) (x (value 30)))
