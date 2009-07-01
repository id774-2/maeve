(define-module core)
(select-module core)

(il (define-immediate-types integer char misc))

(define-macro (define/auto-imm-ref lmd-lst . es)
  (use util.match)
  (match-let1
   (name . params) lmd-lst
   `(define ,lmd-lst
      (il
       ,@(map (lambda (x) `(set! ,x (immediate-ref ,x)))
	      params))
      ,@es)))

(define-macro (define/auto-imm-ref&make-scm:int lmd-lst . es)
  `(define/auto-imm-ref ,lmd-lst
     ,@es
     (il (set! (result 0) (make-immediate integer (result 0))))))

(define/auto-imm-ref&make-scm:int (fx- n m) (il (set! (result 0) (- n m))))
(define/auto-imm-ref&make-scm:int (fx+ n m) (il (set! (result 0) (+ n m))))
(define/auto-imm-ref&make-scm:int (fx* n m) (il (set! (result 0) (* n m))))

(define/auto-imm-ref (fx<? n m)
  (il
   (if (< n m)
     (set! (result 0) (misc-const #t))
     (set! (result 0) (misc-const #f)))))

(define/auto-imm-ref (fx=? n m)
  (il
   (if (= n m)
     (set! (result 0) (misc-const #t))
     (set! (result 0) (misc-const #f)))))

(define (unsafe:zero? n) (fx=? n 0))
(define (false?   x) (fx=? x (il (misc-const #f))))
(define (true?    x) (fx=? x (il (misc-const #t))))
(define (null?    x) (fx=? x (il (misc-const ()))))
(define (eof?     x) (fx=? x (il (misc-const eof))))
(define (undef?   x) (fx=? x (il (misc-const undef))))
(define (unbound? x) (fx=? x (il (misc-const unbound))))

(define false   (il (misc-const #f)))
(define true    (il (misc-const #t)))
(define null    (il (misc-const ())))
(define eof     (il (misc-const eof)))
(define undef   (il (misc-const undef)))
(define unbound (il (misc-const unbound)))

;; arithmetic operator without type check
(define - fx-)
(define + fx+)
(define * fx*)
(define < fx<?)
(define = fx=?)
(define zero? unsafe:zero?)

(define (display n)
  (let1 x (il (immediate-ref n))
    (il (call-c-function printf "%d" x))))

(define (newline) (il (call-c-function puts "")))
(define (print n) (display n) (newline))

(define (print-as-decimal n) (il (call-c-function printf "%d\n" n)))

(define (display-string s) (il (call-c-function printf "%s" s)))
(define (print-string s) (il (call-c-function printf "%s\n" s)))


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

(export pair? vector? cons car cdr make-vector vector-set! vector-ref vector-length
	fx+ fx- fx* fx=? fx<?
	= - + * < zero?
	false? true? null? eof? undef? unbound?
	false  true  null  eof  undef  unbound
	print display newline
	print-as-decimal display-string print-string
	)