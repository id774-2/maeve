(define-module maeve.lib.gauche.debug
  (use gauche.parameter)
  (export-all))

(select-module maeve.lib.gauche.debug)

(define debug-types '())

(define-macro (define-debug-type name)
  (let1 debug? (string->symbol #`",|name|?")
    (push! debug-types name)
    `(begin
       (define ,debug? (make-parameter #f))
       (define-macro (,(string->symbol #`"when-,|name|") . es)
	 `(when (,,debug?) ,@es)))))

(define-debug-type debug)
(define-debug-type debug:regalloca)
(define-debug-type debug:flowgraph)
(define-debug-type debug:normalize)

(define-macro (parse-debug-option)
  (let1 xs (map (lambda (x)
		  (cons
		   (rxmatch-substring (#/^debug\:(.+)$/ (x->string x)) 1)
		   (string->symbol #`",|x|?")))
		debug-types)
  `(lambda (x)
     (case/equal
      x
      (("all")
       ,@(map (lambda (x)
		`(,(cdr x) #t))
	      xs))
      ,@(map (lambda (x)
	       `((,(car x)) (,(cdr x) #t)))
	     xs)))))

(provide "maeve/lib/gauche/debug")