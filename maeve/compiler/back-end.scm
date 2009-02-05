(define-module maeve.compiler.back-end
  ;; MIR -> Assembly
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (export-all))

(select-module maeve.compiler.back-end)

(define *sp* (make-svar :type 'sp))
(define *fp* (make-svar :type 'fp))

(define-values (ref-stack-by-sp/const ref-stack-by-fp/const)
  (let1 gen
      (lambda (base offset)
	(unless (integer? offset) (error "mem offset must be ingeter :" offset))
	(make-mem :base base :offset (* (variable-size) offset)))
    (values (cut gen *sp* <>) (cut gen *fp* <>))))

(define *user-main-symbol* 'user_main)

(define (proc-parameter-allocation:stack type xs)
  ;; (num-of-registers)
  (let* ((n 0)
	 (ys
	  (map1-with-index
	   (lambda (i _)
	     (inc! n)
	     (case type
	       ((lmd)  (ref-stack-by-fp/const i))
	       ((call) (ref-stack-by-sp/const i))
	       (else (error "invalid procparam type :" type))))
	   xs)))
    (values ys (* (variable-size) n))))

(define (register-allocation-with-no-register paramalloca e)
  (let ((lva-table (make-hash-table 'eq?))
	(cur-table (make-hash-table 'eq?)))
    (define cur-default (make-vector (num-of-registers) #f))
    (mir-traverse
     (target e)
     (type no-update)
     (handler
      (lmd
       (let-values (((vec) (vector-copy cur-default))
		    ((dists arg-size) (paramalloca 'lmd param)))
	 (for-each
	  (lambda (lv e)
	    (hash-table-put! lva-table lv e)
	    (when (register? e)
	      (vector-set! vec (register:num-of e) #t)))
	  param dists)
	 (hash-table-put! cur-table *self* vec)
	 (for-each-with-index
	  (lambda (i lv)
	    (hash-table-put!
	     lva-table lv (ref-stack-by-fp/const (- (+ 1 i)))))
	  local-vars)))))
    (when-debug (hash-table-dump lva-table))
    (make-register-allocation-result
     :compute-using-register
     (lambda (xs) (hash-table-get cur-table (find lmd? xs) cur-default))
     :lvar-allocation (lambda (_ lv) (hash-table-get lva-table lv)))))

(define (compute-env-overwrite dists srcs make-key make-mov make-tmp copy-tmp ht-type)
  (let* ((eq-fn (eval ht-type (current-module)))
	 (memkey (cut member <> <> eq-fn))
	 (ht (make-hash-table ht-type)) (nneg 0) (npos 0)
	 (src-keys  (map make-key srcs))
	 (dist-keys (map make-key dists)))
    (for-each-with-index
     (lambda (i dk)
       (when (memkey dk src-keys)
	 (hash-table-put! ht dk i)))
     dist-keys)
    (for-each-with-index
     (lambda (si sk)
       (when (memkey sk dist-keys)
	 (hash-table-update!
	  ht sk
	  (lambda (di)
	    (rlet1 r (- si di)
		   (cond
		    ((negative? r) (inc! nneg))
		    ((positive? r) (inc! npos)))))
	  #f)))
     src-keys)
    (let ((pred (if (> nneg npos) (cut <= 0 <>) (cut >= 0 <>)))
	  (s1 '()) (s2 '()) (s3 '())
	  (broken '()))
      (for-each
       (lambda (d dk s sk)
	 (when (memkey sk broken)
	   (error "compute-env-overwrite : fuck-up! : " srcs dists))
	 (cond
	  ((pred (hash-table-get ht dk 0))
	   (push! s2 (make-mov d s))
	   (push! broken dk))
	  (else
	   (let1 tmp (make-tmp)
	     (push! s1 (make-mov tmp s))
	     (push! s3 (make-mov d (copy-tmp tmp)))))))
       dists dist-keys srcs src-keys)
      (append (reverse! s1) (reverse! s2) (reverse! s3)))))

(define-values (make-inc* make-dec*)
  (let1 mk
      (lambda (opr d s)
	(insert-code*
	 (not (zero? s))
	 (make-set!
	  :dist d
	  :src (make-opr2 :opr opr :v1 d :v2 (make-const :v s)))))
    (values (cut mk '+ <> <>) (cut mk '- <> <>))))

(define stack:free   (cut make-inc* *sp* <>))
(define stack:alloca (cut make-dec* *sp* <>))



(define (vector-memq obj vec)
  (let ((end (vector-length vec)) (r #f))
    (do ((i 0 (+ i 1)))
	((or (>= i end)
	     (and
	      (eq? obj (vector-ref vec i))
	      (begin (set! r #t) #t)))))
    r))

(define (change-syntax-level:medium->low regalloca paramalloca e)
  (define vsize (variable-size))
  (define (%make-seq x) (if (length=1? x) (car x) (make-seq :es x)))
  (define large-const->lbl (make-hash-table 'eqv?))
  (define user-entry-point #f)
  (decompose-register-allocation-result (regalloca paramalloca e))
  (mir-traverse
   (target e)
   (use-circular-graph?)
   (inherited-attr
    (eplogue '() *inherit*)
    (use-call-result-seq '() *init*))
   (extra-code:loop
    (define (compute-temp-space num . opt-no-reglst)
      (define (vector-for-each-with-index-and-escape proc vec)
	(let1 len (vector-length vec)
	  (let loop ((i 0))
	    (unless (= i len)
	      (unless (proc i (vector-ref vec i))
		(loop (+ i 1)))))))
      (let ((dead-reg '()) (rc 0)
	    (using (compute-using-register *parent-nodes*)))
	(for-each
	 (lambda (i) (vector-set! using i #t))
	 (get-optional opt-no-reglst '()))
	(vector-for-each-with-index-and-escape
	 (lambda (i e)
	   (and (not e)
		(begin (push! dead-reg (make-register :num i))
		       (inc! rc) (>= rc num))))
	 using)
	(dotimes (i (- num rc))
	  (push! dead-reg (ref-stack-by-sp/const (- (+ 1 i)))))
	dead-reg))
    (define (%make-set! dist src . opt-make-set)
      (define (%set! d s) (make-set! :dist d :src s))
      (let1 mk (get-optional opt-make-set %set!)
	(cond
	 ((every* mem? dist src)
	  (let1 tmp (car (compute-temp-space 1))
	    (if (register? tmp)
	      (%make-seq (list (%set! tmp src) (mk dist tmp)))
	      (let1 r (make-register :num 0)
		(%make-seq (list (%set! tmp r)  (%set! r src)
				 (mk dist r) (%set! r tmp)))))))
	 (else (mk dist src)))))
    (define (make-set!-sequence dists srcs)
      (compute-env-overwrite
       dists srcs
       (rec
	(loop x)
	(cond
	 ((mem? x) (list 'mem (mem:offset-of x) (loop (mem:base-of x))))
	 ((register? x) (cons 'register (register:num-of x)))
	 ((result? x) (cons 'result (result:num-of x)))
	 ((svar? x) (cons 'svar (svar:type-of x)))
	 ((const? x) (cons 'const (const:v-of x)))
	 (else (il:id x))))
       %make-set!
       (let1 tmps
	   (compute-temp-space
	    (ceiling (/. (length dists) 2))
	    (filter-map1
	     (lambda (x)
	       (cond
		((and (register? x) (register:type-of x))
		 number? => identity)
		(else #f)))
	     dists))
	 (lambda () (pop! tmps)))
       identity 'equal?)))
   (handler
    (cunit
     (let1 c-defs (map
		   (lambda (c)
		     (let1 lbl (make-label
				:name (symbol-append "const_" (il:id c)))
		       (hash-table-put! large-const->lbl c lbl)
		       (%make-deflabel lbl c 'data)))
		   large-consts)
       (begin0
	 (*update!* :es (append c-defs (map loop-s es)))
	 (when user-entry-point
	   (cunit:entry-point-set! *self* user-entry-point)))))
    (const
     (case/pred
      v
      (large-const-type? (hash-table-get large-const->lbl *self*))
      (small-const-type? (*update!*))
      (else (error "Unsupported constant type (1st) :" *self*))))
    (deflabel
      (unless (label? lbl) (error "Invalid label of deflabel :" lbl))
      (let1 data-definition? (not (lmd? e))
	(when (eq? 'main (label:name-of lbl))
	  (label:name-set! lbl *user-main-symbol*)
	  (set! user-entry-point lbl))
	(if data-definition?
	  (*update!* :place 'data)
	  (let1 nl (il:set-new-id! (il:copy lbl))
	    (update! (label:name-of nl) (cut symbol-append <> "_entity"))
	    (make-seq :es (list (%make-deflabel nl (loop-s e))
				(*update!* :e nl :place 'data)))))))
    (lmd
     (receive (_ sp+:param) (paramalloca 'lmd param)
       
       (let* ((nlvars (map loop-s local-vars))
	      (sp+:lvar (fold
			 (lambda (x n) (if (mem? x) (+ vsize n) n))
			 0 nlvars)))
	 (*update!*
	  :local-vars nlvars
	  :es `(,(%make-set! *fp* *sp*)
		,@(stack:alloca sp+:lvar)
		,@(map (*cut-loop*
			:self <>
			:eplogue
			`(,@(stack:free (+ sp+:lvar sp+:param))
			  ,(make-foreign-code :name "gas" :code '("ret"))))
		       es))))))
    (block
     (case/pred
      *self*
      (block-has-not-succ? (*update!* :es (map loop-s (append es eplogue))))
      (block-has-opt-succ?
       (let1 ntest
	   (%make-set! (loop-s (opr2:v1-of test)) (loop-s (opr2:v2-of test))
		       (lambda (u v) (opr2:slot-set!* test :v1 u :v2 v)))
	 (receive (extra nntest)
	     (if (seq? ntest)
	       (receive (l o) (last+others (seq:es-of ntest))
		 (cond
		  ((eq? l test) (values o l))
		  (else
		   (values
		    (seq:es-of ntest)
		    (make-dummy-test :opr (opr2:opr-of* test))))))
	       (values '() ntest))
	   (*update!*
	    :test nntest :es (map loop-s (append es extra))))))
      (else (*update!*))))
    (call
     (define (vector-filter-map1->list-with-index proc vec)
       (let1 r '()
	 (dotimes (i (vector-length vec))
	   (let1 x (proc i (vector-ref vec i))
	     (and x (push! r x))))
	 (reverse! r)))
     (let*-values
	 (((cont-block) (make-block))
	  ((save-regs)
	   (cons
	    *fp*
	    (vector-filter-map1->list-with-index
	     (lambda (i slv) (and slv (make-register :num i)))
	     (compute-using-register *parent-nodes*))))
	  ((misc) `(,(make-block-addr :name (il:id cont-block)) ,@save-regs))
	  ((dists sp+:param) (paramalloca 'call args))
	  ((sp+:misc) (* vsize (length misc)))
	  ((misc:push-seq misc:pop-seq)
	   (filter-map2-with-index
	    (lambda (i src)
	      (update! src loop-s)
	      (values
	       (%make-set! (ref-stack-by-sp/const (+ i (/ sp+:param vsize)))
			   src)
	       (%make-set! src (ref-stack-by-sp/const (- i 1)))))
	    misc)))
       ;;        (map2-with-index
       ;; 	(lambda (i s)
       ;; 	  (values
       ;; 	   (list s (* 8 (+ i (/ 16 8))))
       ;; 	   (list s (* 8 (- i 1)))))
       ;; 	'(r-addr fp r0 r1 rk))
       ;; ((r-addr 16) (fp 24) (r0 32) (r1 40) (rk 48))
       ;; ((r-addr -8) (fp  0) (r0  8) (r1 16) (rk 24))


       (%make-seq
	(list
	 (make-block
	  :default-succ (loop-s proc)
	  :es (append (stack:alloca (+ sp+:param sp+:misc))
		      misc:push-seq
		      (make-set!-sequence dists (map loop-s args))))
	 (block:es-set!
	  cont-block
	  `(,(cadr misc:pop-seq) ,@(stack:free (- sp+:misc vsize))
	    ,@use-call-result-seq
	    ;; return addr was poped.
	    ,@(cddr misc:pop-seq)))))))
    (set!-vls
     (define (make-useq)
       (call-with-values
	   (cut map2-with-index
		(lambda (i v) (values (loop-s v) (make-result :num i)))
		dists)
	 make-set!-sequence))
     (case/pred
      src
      ((value-element? opr1? opr2?)
       (%make-set! (loop-s (car dists)) (loop-s src)))
      ((vls? foreign-code?)
       (%make-seq (cons (loop-s src) (make-useq))))
      (call?
       (*loop* :self src :use-call-result-seq (make-useq)))
      (else
       (error "Unknown set!-vls src type :" src))))
    (vls
     (%make-seq
      (map1-with-index
       (lambda (i e) (%make-set! (make-result :num i) (loop-s e)))
       es)))
    (lvar (lvar-allocation *parent-nodes* *self*)))))

(define (low-level-code->x86+x86-64 expr)
  (define (vnum->byte x) (* (variable-size) x))
  (define lbl->gas-symbol (make-hash-table 'eqv?))
  (define gas-symbols (make-hash-table 'string=?))
  (define data-code '())
  (define code-assert
    (case (arch)
      ((x86-32) ".code32\n")
      ((x86-64) "")
      (else (error "Unknown arch :" (arch)))))
  (define sp #`"%,(stack-pointer)")
  (define fp #`"%,(frame-pointer)")
  (define-values (insn-suffix var-directive)
    (case (variable-size)
      ((4) (values "l" ".long"))
      ((8) (values "q" ".quad"))
      (else (error "Unsupported variable-size :" (variable-size)))))
  (let1 text-code
      (mir-traverse
       (use-circular-graph?)
       (target expr)
       (inherited-attr
	(label-prefix-jump-mode?  #f *init*)
	(const-prefix-required?   #t *init*)
	(label-conv-extra-prefix '() *init*)
	(deflabel-value? #f *init*))
       (extra-code:loop
	(define (label: name thunk)
	  (list
	   (if label-prefix-jump-mode?
	     "" (if (parent-is-a-mem?) ""  "$"))
	   (case name
	     ((main) name)
	     (else (list label-conv-extra-prefix (thunk))))))
	(define-values
	  (cmp->jmp jmp-oprs)
	  (let1 xs
	      '((#f . jmp) (= . je) (< . jl) (> . jg) (<= . jge) (>= . jle))
	    (values (alist->hash-table xs 'eq?) (map cdr xs)))))
       (extra-code:clause
	(define (loop:inherit-lsm s)
	  (*loop* :self s :label-prefix-jump-mode? label-prefix-jump-mode?))
	(define (loop:jump-lsm s)
	  (*loop* :self s :label-prefix-jump-mode? #t))
	(define (operand: x . ctx+)
	  (case/pred
	   x
	   (il? (loop-s x))
	   (string? (write-to-string x))
	   (((cut vector-memq <> (registers))
	     (cut vector-memq <> (special-registers))) (list "%" x))
	   (list? x)
	   (else  (error "Bad operand :" x))))
	(define (insn*: opc . oprs)
	  (list opc
		(if (memq opc jmp-oprs)
		  ""
		  insn-suffix)
		" " (intersperse ", " oprs)
		"\n"))
	(define (insn: opc . oprs) (apply insn*: opc (map operand: oprs)))
	(define (%make-jmp jmp tgt)
	  (insn*: jmp (list (if (any-pred* mem? register? tgt) "*"  "")
			    (loop:jump-lsm tgt)))))
       (handler
	(with-mod (with-mod:body-of (*update!*)))
	(sel-mod (*next-handler*) '())
	(seq (map loop-s es))
	(lmd (map loop-s es))
	(mem
	 (let1 r (loop:inherit-lsm base)
	   (cond
	    (label-prefix-jump-mode? r)
	    ((label? base) r)
	    (else (list offset "(" r ")")))))
	(cunit
	 (list
	  (when entry-point
	    (list ".globl main\nmain:\n"
		  (when init-point
		    (%make-jmp 'call (make-mem :base init-point)))
		  (%make-jmp 'call (make-mem :base entry-point))
		  (insn*: "ret")))
	  ;; 	    (map
	  ;; 	     (lambda (gv) (list ".globl " (loop:jump-lsm gv) "\n"))
	  ;; 	     exported-gvars)
	  (map loop-s es)))
	(foreign-code
	 (if (not (equal? name "gas"))
	   *self*
	   (list (trans-il-in-list loop-s code) "\n")))
	(deflabel
	  (unless (label? lbl) (error "Invalid label of deflabel :" lbl))
	  (let* ((data-definition? (eq? place 'data))
		 (code
		  (list
		   "\n"
		   (*loop*
		    :self (il:copy lbl)
		    :label-prefix-jump-mode? #t
		    :label-conv-extra-prefix
		    (list "# " (label:name-of lbl) "\n"))
		   ":"
		   (if data-definition? " " "\n")
		   (if e (*loop*
			  :self e 
			  :deflabel-value? #t :label-prefix-jump-mode? #t
			  :const-prefix-required?  (not data-definition?))
		       '()))))
	    (if data-definition?
	      (begin (push! data-code code) '())
	      code)))
	(label
	    ;; GAS label prefix :
	    ;;      imm mem
	    ;; jmp       *
	    ;; else  $
	    (list
	     (when deflabel-value? (list var-directive " "))
	     (label:
	      name
	      (mcut
	       cond
	       ((hash-table-get lbl->gas-symbol id #f) => identity)
	       (else
		(rlet1
		 x (with-string-io (x->string name)
		     (lambda ()
		       (port-for-each
			(lambda (c)
			  (write-char
			   (if (char-set-contains? #[\w] c)
			     c #\_)))
			read-char)))
		 (hash-table-update!
		  gas-symbols x
		  (lambda (n) (update! x (cut list <> n)) (+ 1 n))
		  0)
		 (hash-table-put! lbl->gas-symbol id x)))))))
	(block-addr
	 (label: #f (lambda () #`"block_,|name|")))
	(block
	 (list (*loop* :self (make-block-addr :name id)
		       :label-prefix-jump-mode? #t)
	       ":\n" (map loop-s es)
	       (when (block-has-opt-succ? *self*)
		 (receive (%cmp %jmp)
		     (let1 err
			 (cut error "Invalid opr2 in test of opt-succ :" *self*)
		       (values
			'cmp
			(cond
			 ((hash-table-get
			   cmp->jmp
			   (or (opr2:opr-of* test)
			       (dummy:opr-of* test) (err))) => identity)
			 (else (err)))))
		   (list (when (opr2? test)
			   (let-decompose-opr2
			    test
			    (receive (d s)
				(if (const? v1)
				  (values v1 v2)
				  (values v2 v1))
			      (insn*: %cmp (loop-s d) (loop-s s)))))
			 (%make-jmp %jmp opt-succ))))
	       (when default-succ
		 (%make-jmp 'jmp default-succ))))
	(opr2 (error "Invalid opr2 as statement :" *self*))
	;; 	  (aasm:stack-allocate
	;; 	   (insn: 'sub (make-hlf:const :value (vnum->byte vnum))
	;; 		  sp))
	;; 	  (aasm:stack-free
	;; 	   (insn: 'add (make-hlf:const :value (vnum->byte vnum))
	;; 		  sp))
	(opr1
	 (case opr
	   ((-) (insn*: 'neg (loop-s v)))
	   (else (error "Unkown operator of opr1 :" *self*))))
	(set!
	 (define sopr2
	   (alist->hash-table
	    '((+ . add) (- . sub) (* . imul) (/ . div))
	    'eq?))
	 (if (opr2? src)
	   (let-decompose-opr2
	    src
	    (cond
	     ((hash-table-get sopr2 opr #f)
	      => (lambda (rop)
		   (cond
		    ((eq? v1 dist) (insn*: rop (loop-s v2) (loop-s dist)))
		    ((eq? v2 dist) (insn*: rop (loop-s v1) (loop-s dist)))
		    (else
		     (let1 d (loop-s dist)
		       (list (insn*: 'mov (loop-s v1) d)
			     (insn*:  rop (loop-s v2) d)))))))
	     (else (error "Invalid opr2 in dist of set! :" *self*))))
	   (insn*: 'mov (loop-s src) (loop-s dist))))
	(const
	 (receive (direc val)
	     (case/pred
	      v
	      (((cut (make-misc-immidiate) <> #f))
	       => (cut values var-directive <>))
	      (integer? (values var-directive v))
	      ((and large-const-type?
		    (lambda _ deflabel-value?))
	       (case/pred
		v
		(string? (values ".asciz" (write-to-string v)))
		(else (error "Unsupported constant type (2nd) : " *self*))))
	      (else (error "Unsupported constant type (3rd) : " *self*)))
	   (if deflabel-value?
	     (list direc " " val)
	     (list (if const-prefix-required? "$" "") val))))
	;; 	  (aasm:stack
	;; 	   (list (vnum->byte offset)
	;; 		 "(%" (if use-stack-pointer?
	;; 			sp fp)")"))
	(register
	 (operand:
	  (if (and (integer? num)
		   (<= 0 num (- (num-of-registers) 1)))
	    (vector-ref (registers) num)
	    (error "Unknown register number :" num))))
	(result
	 (operand:
	  (if (and (integer? num)
		   (<= 0 num (- (num-of-registers) 1)))
	    (vector-ref (registers) num)
	    (error "Unsupported result number :" num))))
	(svar
	 (case type
	   ((sp) sp) ((fp) fp)
	   (else (error "Unknown svar type :" type))))))
    (list code-assert "\n.data\n" data-code "\n.text\n" text-code "\n")))

;;     (seq (map loop-s es))
;;     (label name)
;;     (lvar)
;;     (svar (case type ((sp) sp) ((fp) fp) (else (err))))
;;     (result (vector-ref regs num))
;;     (register (vector-ref regs num))
;;     (const v)
;;     (mem
;;      (let1 o (if offset (loop-s offset) 0)
;;        (unless (number? o) (err))
;;        (list offset "(" (loop-s base) ")")))
;;     (elt)
;; (opr2) (op1)
;;     (foreign-code
;;      (if (not (equal? name "gas"))
;;        *self*
;;        (list (trans-il-in-list loop-s code) "\n")))
;;     (with-mod (with-mod:body-of (*update!*)))
;;     (selmod (*next-handler*) '())
;;     (mod '())

(provide "maeve/compiler/back-end")