(module test (main main))

(define (foo a b c d e f g)
  (display a) (newline)
  (display b) (newline)
  (display c) (newline)
  (display d) (newline)
  (display e) (newline)
  (display f) (newline)
  (display g) (newline)
  (bar (+ a b) (+ b c) (+ c d) (+ d e) (+ e f) (+ f g) (+ g a)))

(define (bar a b c d e f g)
  (display a) (newline)
  (display b) (newline)
  (display c) (newline)
  (display d) (newline)
  (display e) (newline)
  (display f) (newline)
  (display g) (newline)
  (foo (- a b) (- b c) (- c d) (- d e) (- e f) (- f g) (- g a)))

(define (main arg)
  (print arg)
  (bar 1 2 3 4 5 6 7)
  (foo 11 22 33 44 55 66 77)
  (bar 111 222 333 444 555 666 777)
  (foo 1111 2222 3333 4444 5555 6666 7777)
  (bar 11111 22222 33333 44444 55555 66666 77777)
  (foo 111111 222222 333333 444444 555555 666666 777777))

(define (foo a b c d e f g)
  (display a) (newline)
  (display b) (newline)
  (display c) (newline)
  (display d) (newline)
  (display e) (newline)
  (display f) (newline)
  (display g) (newline)
  (let ((G8 (+ a b))
	(G9 (+ b c))
	(G10 (+ c d))
	(G11 (+ d e))
	(G12 (+ e f))
	(G13 (+ f g))
	(G14 (+ g a)))
    (call-with-no-continuation bar G8 G9 G10 G11 G12 G13 G14)))

;; (define (bar a b c d e f g)
;;   (display a) (newline)
;;   (display b) (newline)
;;   (display c) (newline)
;;   (display d) (newline)
;;   (display e) (newline)
;;   (display f) (newline)
;;   (display g) (newline)
;;   (foo (- a b) (- b c) (- c d) (- d e) (- e f) (- f g) (- g a)))

;; (list-ec
;;  (: i 0 6)
;;  `(,(if (odd? i) 'foo 'bar)
;;    ,@(map
;;       (lambda (s)
;; 	(string->number
;; 	 (apply string-append
;; 		(list-ec (: _ 0 (+ 1 i)) s))))
;;       '("1" "2" "3" "4" "5" "6" "7"))))

