(define-module ack
  (import immediate-type)
;;   (define (ack m n)
;;     (il (call-c-function printf "%d %d\n" n m))
;;     (if (zero? m)
;;       (begin
;; 	(print-string "point 0")
;; 	(+ n 1))
;;       (if (zero? n)
;; 	(begin
;; 	  (print-string "point 1")
;; 	  (ack (- m 1) 1))
;; 	(begin
;; 	  (print-string "point 2")
;; 	  (ack (- m 1)
;; 	       (begin
;; 		 (print-string "point 3")
;; 		 (ack m (- n 1))))))))
  
  (define (ack m n)
    (if (zero? m)
      (+ n 1)
      (if (zero? n)
	(ack (- m 1) 1)
	(ack (- m 1)
	     (ack m (- n 1))))))

  (define (main)
;;     (print (ack 0 0)) ;; 1
;;     (print (ack 0 1)) ;; 2
;;     (print (ack 1 0)) ;; 2
;;     (print (ack 1 1)) ;; 3
;;     (print (ack 1 2)) ;; 4
;;     (print (ack 2 1)) ;; 5
;;     (print (ack 2 2)) ;; 7
;;     (print (ack 3 2)) ;; 29
;;     (print (ack 2 3)) ;; 9
;;     (print (ack 3 3)) ;; 61
    (print (ack 3 12))
    (main)
    ))