(define-module maeve.lib.gauche.pp
  (use srfi-1)
  (use srfi-43)
  (use util.list)
  (use util.match)
  (use text.tree)
  (use gauche.sequence)
  (export pretty-print x->pp))

(select-module maeve.lib.gauche.pp)

(define-reader-ctor 'hash-table alist->hash-table)

;; <doc> =
;;      | ()                    (nil)
;;      | "..."                 (text)
;;      | #\newline             (line)
;;      | (<integer> <doc> ...) (nest)
;;      | (group <doc> ...)     (group)
;;      | (<doc> ...)           (cons)

(define (pp-fits? width xs)
  (and (not (negative? width))
       (match xs
         (() #t)
         (((i m ()) ys ...)
          (pp-fits? width ys))
         (((i m ('group doc ...)) ys ...)
          (pp-fits? width (cons (list i 'flat doc) ys)))
         (((i m ([? integer? j] x ...)) ys ...)
          (pp-fits? width
                   (cons (list (+ i j) m x) ys)))
         (((i m [? string? s]) ys ...)
          (pp-fits? (- width (string-length s)) ys))
         (((i 'flat #\newline) ys ...)
          (pp-fits? (- width 1) ys))
         (((i 'break #\newline) ys ...)
          #t)
         (((i m (y1 . ys)) zs ...)
          (pp-fits? width
                    (cons* (list i m y1) (list i m ys) zs))))))

(define (pp-make-tree width k xs)
  (match
   xs
   (() "")
   (((i m ()) ys ...)
    (pp-make-tree width k ys))
   (((i m ('group doc ...)) ys ...)
    (let1 mode (if (pp-fits? (- width k) (cons (list i 'flat doc) ys))
		 'flat
		 'break)
      (pp-make-tree width k (cons (list i mode doc)
				  ys))))
   (((i m ([? integer? j] x ...)) ys ...)
    (pp-make-tree
     width k
     (cons (list (+ i j) m x)
	   ys)))
   (((i m [? string? s]) ys ...)
    (cons
     s
     (pp-make-tree
      width
      (+ k (string-length s))
      ys)))
   (((i 'flat #\newline) ys ...)
    (cons
     #\space
     (pp-make-tree width (+ k 1) ys)))
   (((i 'break #\newline) ys ...)
    (cons*
     #\newline
     (make-string i #\space)
     (pp-make-tree width i ys)))
   (((i m (y1 . ys)) zs ...)
    (pp-make-tree
     width k
     (cons*
      (list i m y1)
      (list i m ys)
      zs)))))

(define x->pp
  (lambda (obj memo ss-counter use-eq-hash) 
    (define (complex-object? obj)
      (or (pair? obj) (vector? obj) (string? obj) (hash-table? obj)))
    (define (scan obj)
      (cond
       ((not (complex-object? obj)))
       ((hash-table-exists? memo obj)
	(unless (hash-table-get memo obj)
	  (hash-table-put! memo obj #t)))
       (else
	(hash-table-put! memo obj #f)
	(cond ((pair? obj)
	       (scan (cdr obj))
	       (scan (car obj)))
	      ((vector? obj)
	       (vector-for-each
		(lambda (_ e) (scan e))
		obj))
	      ((hash-table? obj)
	       (hash-table-for-each
		obj (lambda (k v) (scan k) (scan v))))
	      (else #f)))))
    (define (trans obj)
      (define (check-memo obj)
	(and
	 (complex-object? obj)
	 (let1 v (hash-table-get memo obj)
	   (cond
	    ((not v) #f)
	    ((number? v)
	     (if use-eq-hash
	       #`"#,(eq-hash obj)#"
	       #`"#,|v|#"))
	    (else
	     (let* ((n (inc! ss-counter))
		    (tag (if use-eq-hash
			   #`"#,(eq-hash obj)="
			   #`"#,|n|=")))
	       (hash-table-put! memo obj n)
	       (list
		tag
		(string-length tag)
		(make-spec obj))))))))
      (define (make-spec obj)
	(cond
	 ((is-a? obj <list>)
	  (match
	   obj
	   (() "()")
	   (('quote obj)
	    (list "'" (trans obj)))
	   (('quasiquote obj)
	    (list "`" (trans obj)))
	   (('unquote obj)
	    (list "," (trans obj)))
	   (('unquote-splicing obj)
	    (list ",@" (trans obj)))
	   (('define (name&args ..1) body ..1)
	    `(group "(define " (group (8 ,@(trans name&args)))
		    (2 #\newline (group ,@(map trans body)))
		    ")"))
	   (_
	    (let loop ((xs (cdr obj))
		       (rs (list (trans (car obj)))))
	      (define (dot-pair-case r)
		(loop '() (cons* r #\newline "." #\newline rs)))
	      (cond
	       ((check-memo xs)
		=> (lambda (r) (dot-pair-case r)))
	       ((null? xs)
		`(group "(" (1 ,@(reverse rs)) ")"))
	       ((pair? xs)
		(loop (cdr xs) (cons* (trans (car xs)) #\newline rs)))
	       (else
		(dot-pair-case (trans xs))))))))
	 ((is-a? obj <vector>)
	  `(group "#(" (2 ,@(intersperse #\newline
					 (map trans (vector->list obj)))) ")"))
	 ((is-a? obj <hash-table>)
	  
	  ;; 	  (format #f "#,(hash-table ~s ~s)"
	  ;; 		  (hash-table-map
	  ;; 		   obj (lambda (k v) (cons (trans k) (trans v))))
	  ;; 		  (hash-table-type obj))
	  ;; `(group "#,(hash-table"
	  ;; 		  (2 ,
	  ;; 		     (hash-table-type obj))
	  ;; 		  ")")
	  `(group "#,(hash-table"
		  #\newline "("
		  ,(intersperse
		    #\newline
		    (hash-table-map
		     obj (lambda (k v)
			   (list "(" (trans k) #\newline "." #\newline
				 (trans v) ")"))))
		  ")" #\newline ,(trans (hash-table-type obj)) ")"))
	 (else
	  (write-to-string obj))))
      (cond
       ((check-memo obj) => values)
       (else (make-spec obj))))

    ;; driver
    (scan obj)
    (let1 r (trans obj)
      (values r ss-counter))))

(define pretty-print
  (let ((common-table (make-hash-table 'eq?))
	(common-ss-counter -1))
    (lambda (obj . ex)
      (let-keywords
       ex
       ((use-global-table? #f)
	(use-eq-hash #f)
	(port (current-output-port))
	(width 78))
       (let ((pp
	      (if use-global-table?
		(receive (r nc)
		    (x->pp obj common-table
			   common-ss-counter use-eq-hash)
		  (set! common-ss-counter nc)
		  r)
		(x->pp obj (make-hash-table 'eq?) -1 use-eq-hash))))
	 (write-tree (pp-make-tree
		      width 0 `((0 flat ,pp)))
		     port)
	 (newline port)
	 obj)))))

(provide "maeve/lib.gauche/pp")
