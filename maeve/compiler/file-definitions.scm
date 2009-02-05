(define-module maeve.compiler.file-definitions
  (use maeve.lib.gauche.misc)
  (use file.util)
  (export-all))

(select-module maeve.compiler.file-definitions)

(define-macro (%file name suffix)
  (let ((gf (symbol-append "omn->" name "-file"))
	(g (gensym)))
    `(begin
       (define (,gf omn)
	 (build-path (current-directory)
		     "tmp" (string-append (x->string omn) "."
					  ,(x->string suffix))))
       (define (,(symbol-append "call-with-output-" name "-file") omn p)
	 (call-with-output-file (,gf omn) p))
       (define-macro (,(symbol-append "with-output-to-" name "-file") omn . es)
	 `(with-output-to-file (,',gf ,omn)
	    (lambda () ,@es)))
       (define-macro (,(symbol-append "with-output-to-"
				      name "-file*") omn f . es)
	 `(let1 ,',g (begin ,@es)
	    (with-output-to-file (,',gf ,omn)
	      (lambda () (,f ,',g))))))))

(%file mir mir)
(%file asm s)
(%file graphviz dot)
(%file graphviz-object gif)

(provide "maeve/compiler/file-definitions")