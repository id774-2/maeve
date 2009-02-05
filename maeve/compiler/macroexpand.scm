(define-module maeve.compiler.macroexpand
  (use util.match)
  (use maeve.lib.gauche.complex-iterator)
  (use maeve.lib.gauche.values)
  (export-all))

(define (maeve:macroexpand-1 expr)
  )

(define (process-define-macro expr)
  (let loop ((expr expr)
  (match
   expr
   (('define-macro 
