(define-module macro
  (import core)
  (define-macro (foo x) `(print ,x))
  (define-macro (bar x) `(foo ,x))
  (define (main) (bar (* 7 6))))