(use srfi-1)

(define (list<=? eq y x)
  (let loop ((x x) (y y))
    (cond
     ((and (null? x) (null? y))
      #t)
     ((and (pair? x) (pair? y))
      (if (eq (car x) (car y))
	(loop (cdr x) (cdr y))
	(fold (lambda (a b) (or (loop a y) b)) #f x)))
     ((or (null? x) (null? y)) #f)
     (else (eq x y)))))

;; #t になるケース :

(print (list<=? equal? 'x 'x))
(print (list<=? equal? '(a b) '(a b)))
(print
 (list<=?
  equal?
  '(a (b ((c)) d))
  '(x (y) (((((z (a (b ((c)) d))))))))))

;; #f になるケース :

(print (list<=? equal? 'x 'y))
(print (list<=? equal? '(a b c) '(a b)))
(print (list<=? equal? '(a b c) '(b c)))
