(define-module imm)
(select-module imm)

(il (define-immediate-types integer char misc))

(define (fx- n m)
  (il (set! n (immediate-ref n))
      (set! m (immediate-ref m))
      (set! (result 0) (- n m))
      (set! (result 0) (make-immediate integer (result 0)))))

(define (fx+ n m)
  (il (set! n (immediate-ref n))
      (set! m (immediate-ref m))
      (set! (result 0) (+ n m))
      (set! (result 0) (make-immediate integer (result 0)))))

(define (fx* n m)
  (il (set! n (immediate-ref n))
      (set! m (immediate-ref m))
      (set! (result 0) (* n m))
      (set! (result 0) (make-immediate integer (result 0)))))

(define (fx<? n m)
  (il (set! n (immediate-ref n))
      (set! m (immediate-ref m))
      (if (< n m)
	(set! (result 0) (misc-const #t))
	(set! (result 0) (misc-const #f)))))

(define (fx=? n m)
  (il (if (= n m)
	(set! (result 0) (misc-const #t))
	(set! (result 0) (misc-const #f)))))

(define (fact n)
  (if (fx=? n 1)
    1
    (fx* n (fact (fx- n 1)))))

  (define (ack m n)
    (if (fx=? 0 m)
      (fx+ n 1)
      (if (fx=? 0 n)
	(ack (fx- m 1) 1)
	(ack (fx- m 1)
	     (ack m (fx- n 1))))))

(define (print-as-decimal n) (il (call-c-function printf "%d\n" n)))

(define (main)
  (let* ((n (fact 10))
	 (m (il (immediate-ref n)))
	 (x (ack 3 3))
	 (y (il (immediate-ref x))))
    (print-as-decimal m)
    (print-as-decimal y) ;; 61
    (print-as-decimal (il (misc-const undef)))
    (print-as-decimal (il (misc-const unbound)))
    (print-as-decimal (il (misc-const eof)))))