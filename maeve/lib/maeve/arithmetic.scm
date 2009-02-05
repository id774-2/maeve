(define-module arithmetic)
(select-module arithmetic)

(define (unsafe:- n m) (il (set! (result 0) (- n m))))
(define (unsafe:+ n m) (il (set! (result 0) (+ n m))))
(define (unsafe:* n m) (il (set! (result 0) (* n m))))
(define (unsafe:< n m) (il
			(if (< n m)
			  (set! (result 0) (misc-immidate #t))
			  (set! (result 0) (misc-immidate #f)))))
(define (unsafe:= n m) (il
			(if (= n m)
			  (set! (result 0) (misc-immidate #t))
			  (set! (result 0) (misc-immidate #f)))))
(define (unsafe:zero? n) (unsafe:= n 0))
(define (print-as-decimal n) (il (call-c-function printf "%d\n" n)))
(define (false?   x) (unsafe:= x (il (misc-immidate #f))))
(define (true?    x) (unsafe:= x (il (misc-immidate #t))))
(define (null?    x) (unsafe:= x (il (misc-immidate ()))))
(define (eof?     x) (unsafe:= x (il (misc-immidate eof))))
(define (undef?   x) (unsafe:= x (il (misc-immidate undef))))
(define (unbound? x) (unsafe:= x (il (misc-immidate unbound))))

(define false   (il (misc-immidate #f)))
(define true    (il (misc-immidate #t)))
(define null    (il (misc-immidate ())))
(define eof     (il (misc-immidate eof)))
(define undef   (il (misc-immidate undef)))
(define unbound (il (misc-immidate unbound)))

;; arithmetic operator without type check
(define - unsafe:-)
(define + unsafe:+)
(define * unsafe:*)
(define < unsafe:<)
(define = unsafe:=)
(define zero? unsafe:zero?)

(export = - + * < print-as-decimal zero?
	false? true? null? eof? undef? unbound?
	false  true  null  eof  undef  unbound)