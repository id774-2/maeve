(define-module complex-type)
(select-module complex-type)
(import immediate-type)
(il
 (define-complex-type pair 0 car cdr)
 (define-complex-type vector 1 length (elms :unfixed-size? #t))
 (define-complex-type closure 2 lbl length (elms :unfixed-size? #t)))

(define (pair? x) (= 0 (il (mem (elm-addr x pair tag)))))
(define (vector? x) (= 1 (il (mem (elm-addr x vector tag)))))

(define (cons x y) (il (make-complex-object pair :car x :cdr y)))
(define (car x) (il (mem (elm-addr x pair car))))
(define (cdr x) (il (mem (elm-addr x pair cdr))))

(define (make-vector y)
  (il (make-complex-object vector :length y :unfixed-size (* 8 y))))

(define (vector-set! v i x)
  (il (set! (mem (elm-addr v vector elms i)) x)))
(define (vector-ref v i)
  (il (mem (elm-addr v vector elms i))))
(define (vector-length v)
  (il (mem (elm-addr v vector length))))

(export pair? vector? cons car cdr make-vector vector-set! vector-ref vector-length)