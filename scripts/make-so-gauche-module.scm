(use gauche.process)
(use gauche.config)
(use file.util)

(debug-print-width 100000)

(define src-dir ".")
(define this-file-dir (build-path src-dir "scripts"))
(define maeve-gauche-lib-dir (build-path src-dir "lib/gauche"))
(define stub-module-prefix "maeve.lib.gauche")

(define (exec-command str)
  (call-with-input-process #?=str (lambda _)))

(define (make-one stub-extra orig-file-full)
  (receive (dir orig-file suffix) (decompose-path orig-file-full)
    (and-let* ((rx (#/(.+?)-original/ orig-file))
	       (file (rxmatch-substring rx 1)))
      (let1 gc-out (build-path dir file)
	(exec-command #`"gosh gencomp -o ,|gc-out| scripts/,|orig-file-full|"))
      (let* ((cc-in (build-path dir #`",|file|.c"))
	     (cc-out (build-path dir #`",|file|.so"))
	     (so (build-path maeve-gauche-lib-dir cc-out)))
	(exec-command
	 #`"gcc  -fPIC -shared -std=gnu99 -DHAVE_CONFIG_H ,(gauche-config \"-I\") -o ,|cc-out| ,|cc-in|")
	(exec-command #`"mv ,|cc-out| ,|so|")
	(call-with-output-file (build-path maeve-gauche-lib-dir #`",|file|.scm")
	  (lambda (op)
	    (for-each
	     (cut write <> op)
	     (let1 mod #`",|stub-module-prefix|.,|file|"
	       #?=`((define-module ,(string->symbol mod)
		      ,@stub-extra
		      (dynamic-load ,so)
		      (export-all)
		      (provide ,(regexp-replace-all #/\./ mod "/"))))))))))))

(make-one
 '((use srfi-1))
 "complex-iterator-original.scm")