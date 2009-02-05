(define-module maeve.lib.gauche.debug
  (use gauche.parameter)
  (export-all))

(select-module maeve.lib.gauche.debug)

(define debug? (make-parameter #f))

(define-macro (when-debug . es)
  `(when (,debug?) ,@es))

(provide "maeve/lib/gauche/debug")