(debug-print-width 1000)

(use srfi-1)
(use util.match)

;; (define (closure-convert e)
;;   (define (mark e)
;;     (let loop ((e e) (envs '()))
;;       (match
;;        e
;;        (('lambda args es ...)
;; 	`(lambda ,args ,@(map (cut loop <> (cons args envs)) es)))
;;        ((? symbol? s)
;; 	(cond
;; 	 ((find
;; 	   (lambda (e) (memq s e))
;; 	   envs)
;; 	  => (cut list 'lvar s <>))
;; 	 (else s)))
;;        ((xs ...) (map (cut loop <> envs) xs))
;;        (else e))))
;;   (define (add-parameter e)
;;     (let1 extra-envs '()
;;       (let loop ((e e) (envs '()))
;; 	(match
;; 	 e
;; 	 (('lambda args es ...)
;; 	  (push! extra-envs (list #f))
;; 	  (let ((x (map (cut loop <> (cons args envs)) es))
;; 		(reqenvs (remove
;; 			  (lambda (e) (equal? args e))
;; 			  (drop-right (pop! extra-envs) 1))))
;; 	    (for-each (lambda (e) (push! (car extra-envs) e)) reqenvs)
;; 	    `(lambda (,reqenvs ,@args) ,@x)))
;; 	 (('lvar s env)
;; 	  (unless (eq? env (car envs))
;; 	    (update! (car #?=extra-envs) (cut lset-adjoin eq? <> env)))
;; 	  e)
;; 	 ((xs ...) (map (cut loop <> envs) xs))
;; 	 (else e)))))
;;   (define (move-toplevel e)
;;     (let* ((lmds '())
;; 	   (e (let loop ((e e))
;; 		(match
;; 		 e
;; 		 (('lambda args es ...)
;; 		  (let1 name (gensym)
;; 		    (push! lmds `(define ,name (lambda ,args ,@(map loop es))))
;; 		    `(closure ,name ,(car args))))
;; 		 (('lvar _ _) e)
;; 		 ((xs ...) (map loop xs))
;; 		 (else e)))))
;;       `(,@lmds ,e)))
;;   (move-toplevel (add-parameter (mark e))))
       

;; #?=(closure-convert
;;     '((lambda (a b c)
;; 	((lambda (i j k)
;; 	   ((lambda (x y z)
;; 	      (list a b c i j k x y z))
;; 	    6 7 8))
;; 	 3 4 5))
;;       0 1 2))

(define (lset-adjoin/save-order eq lst e)
  (if (member e lst eq) lst (cons e lst)))

(define (closure-convert e)
  (define (mark e)
    (let1 extra-vars '()
      (let loop ((e e) (envs '()))
	(match
	 e
	 (('lambda args es ...)
	  (push! extra-vars (list #f))
	  (let ((x (map (cut loop <> (cons args envs)) es))
		(reqenvs (reverse
			  #?=(remove
			      (lambda (e) (memq e args))
			      (drop-right (pop! extra-vars) 1)))))
	    (for-each (lambda (e) (push! (car extra-vars) e)) reqenvs)
	    `(lambda (,reqenvs ,@args) ,@x)))
	 ((? symbol? s)
	  (cond
	   ((find
	     (lambda (e) (memq s e))
	     envs)
	    =>
	    (lambda (env)
	      (unless (eq? env (car envs))
		(update! (car #?=extra-vars) (cut lset-adjoin/save-order eq? <> s)))
	      e))
	   (else s)))
	 ((xs ...) (map (cut loop <> envs) xs))
	 (else e)))))
  (define (move-toplevel e)
    (let* ((lmds '())
	   (e (let loop ((e e))
		(match
		 e
		 (('lambda args es ...)
		  (let1 name (gensym)
		    (push! lmds `(define ,name (lambda ,args ,@(map loop es))))
		    `(closure ,name ,(car args))))
		 (('lvar _ _) e)
		 ((xs ...) (map loop xs))
		 (else e)))))
      `(,@(reverse! lmds) ,e)))
  (move-toplevel (mark e)))
       

#?=(closure-convert
    '((lambda (a b c)
	((lambda ()
	   ((lambda (i j k)
	      ((lambda (x y z)
		 (cons a (cons j (cons k (cons x (cons y (cons z '())))))))
	       6 7 8))
	    3 4 5))))
      0 1 2))

;; =>
;; ((define G41 (lambda (() . #0=(a b c)) ((closure G42 #1=(#0#)) 3 4 5)))
;;  (define G42 (lambda (#1# . #2=(i j k)) ((closure G43 #3=(#2# #0#)) 6 7 8)))
;;  (define G43
;;    (lambda (#3# . #4=(x y z))
;;      (list (lvar a #0#) (lvar b #0#) (lvar c #0#)
;; 	   (lvar i #2#) (lvar j #2#) (lvar k #2#)
;; 	   (lvar x #4#) (lvar y #4#) (lvar z #4#))))
;;  ((closure G41 ()) 0 1 2))
