(define-module maeve.compiler.back-end
  ;; MIR -> Assembly
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (use maeve.compiler.register-allocation)
  (use maeve.compiler.misc)
  (export-all))

(select-module maeve.compiler.back-end)

(define *user-main-symbol* 'user_main)

(define-values (make-inc* make-dec*)
  (let1 mk
      (lambda (opr d s)
	(insert-code*
	 (not (zero? s))
	 (make-set!
	  :dist d
	  :src (make-opr2 :opr opr :v1 d :v2 (make-asm-int s)))))
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
   (use-debug:print-self?)
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
	    (using (vector-copy
		    (compute-using-register (cons *self* *parent-nodes*)))))
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
      (%make-set!-sequence
       %make-set!
       (let1 tmps
	   (compute-temp-space
	    (+ 1 (ceiling (/. (length dists) 2)))
	    (filter-map1
	     (lambda (x)
	       (cond
		((and (register? x) (register:num-of x)) number? => identity)
		(else #f)))
	     dists))
	 (lambda () (pop! tmps)))
       dists srcs)))
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
    (allocate-cpx
     (decompose-def-cpx-type
      (hash-table-get*
       (mod:type-table-of %current-module)
       type-name (error "Unknown complex type name :" type-name)))
     (let1 size (make-asm-int (* vsize (+ 1 ;; type tag
					  (length general-slots))))
       (*loop*
	:use-call-result-seq use-call-result-seq
	:self (make-call
	       :abi (arch)
	       :proc (make-label :name 'malloc :foregin? #t)
	       :args
	       (list
		(cond
		 ((and unfixed-slot (loop-s unfixed-size))
		  => (mcut make-opr2 :opr '+ :v1 size :v2 <>))
		 (else size)))))))
    (const
     (cond
      ((large-const-type? v)
       (hash-table-get large-const->lbl *self*))
      ((and
	(memq type-name '(scm:bool scm:nil scm:eof
				   scm:undef scm:unbound))
	(or (small-const-type? v)
	    (memq v '(eof undef unbound))))
       (*update!*))
      ((eq? type-name 'scm:integer)
       (loop-s (make-make-imm :type-name 'integer :v *self*)))
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
	     (lambda (i slv) (and (eqv? #t slv)
				  (make-register :num i)))
	     (rlet1
	      cur (compute-using-register (cons *self* *parent-nodes*))
	      (when-debug:regalloca
	       (format #t "~s : ~s ~s\n"
		       (map il:id (cons *self* *parent-nodes*))
		       (eq-hash cur) cur))))))
	  ((misc) (append
		   (insert-code*
		    (not abi) (make-block-addr :name (il:id cont-block)))
		   save-regs))
	  ((dists sp+:param) ((case abi
				((x86-32) proc-parameter-allocation:stack)
				((x86-64) proc-parameter-allocation:x86-64)
				(else paramalloca))
			      'call args))
	  ((sp+:misc) (* vsize (length misc)))
	  ((misc:push-seq misc:pop-seq)
	   (filter-map2-with-index
	    (lambda (i src)
	      (update! src loop-s)
	      (values
	       (%make-set! (ref-stack-by-sp/const (+ i (/ sp+:param vsize)))
			   src)
	       (%make-set! src (ref-stack-by-sp/const
				(- i (if (not abi) 1 0))))))
	    misc)))
       ;; (map2-with-index
       ;;  (lambda (i s)
       ;;   (values
       ;;    (list s (* 8 (+ i (/ 16 8))))
       ;;    (list s (* 8 (- i 1)))))
       ;;  '(r-addr fp r0 r1 rk))
       ;; ((r-addr 16) (fp 24) (r0 32) (r1 40) (rk 48))
       ;; ((r-addr -8) (fp  0) (r0  8) (r1 16) (rk 24))
       (let ((pre-seq (append
		       (stack:alloca (+ sp+:param sp+:misc))
		       misc:push-seq
		       (make-set!-sequence dists (map loop-s args))))
	     (post-seq
	      ;; return addr was poped.
	      `(,((if (not abi) cadr car) misc:pop-seq) ,@use-call-result-seq
		,@((if (not abi) cddr cdr) misc:pop-seq)
		,@(stack:free (- sp+:misc (if (not abi) vsize 0))))))
	 (%make-seq
	  (if abi
	    `(,@pre-seq
	      ,(%make-set! (make-register :num 0) (make-asm-int 0))
	      ,(make-foreign-code :name "gas" :code `("call " ,proc))
	      ,@post-seq)
	    (list
	     (make-block :default-succ proc :es pre-seq)
	     (block:es-set! cont-block post-seq)))))))
    (set!-vls
     (define (make-useq)
       (call-with-values
	   (cut map2-with-index
		(lambda (i v) (values (loop-s v) (make-result :num i)))
		dists)
	 make-set!-sequence))
     (case/pred
      src
      ((value-element? opr1? opr2? make-imm? imm-ref?)
       (%make-set! (loop-s (car dists)) (loop-s src)))
      ((vls? foreign-code?)
       (%make-seq (cons (loop-s src) (make-useq))))
      ((call? allocate-cpx?)
       (*loop* :self src :use-call-result-seq (make-useq)))
      (else
       (error "Unknown set!-vls src type :" src))))
    (vls
     (%make-seq
      (make-set!-sequence
       (map1-with-index
	(lambda (i _) (make-result :num i))
	es)
       (map loop-s es))))
    (lvar (lvar-allocation *parent-nodes* *self*))
    (mem
     (case/pred
      base
      (elm-addr?
       (match-let1
	#(pre base offset) (loop-s base)
	(%make-seq
	 `(,@pre ,(*update!* :base base :offset offset)))))
      (else (*update!*))))
    (elm-addr
     (decompose-def-cpx-type
      (hash-table-get*
       (mod:type-table-of %current-module) type-name
       (error "Unknown complex type name :" type-name)))
     (unless (mem? (car *parent-nodes*))
       (error "elm-addr context fault" (cons *self* *parent-nodes*)))
     (let*-values
	 (((pre) '())
	  ((base offset)
	   (cond
	    ((il? index)
	     (let ((base (loop-s base))
		   (tmp (car (compute-temp-space 1))))
	       (set!
		pre
		`(,(%make-set!
		    tmp
		    (make-opr2
		     :opr '* :v2 (loop-s index) :v1 (make-asm-int vsize)))
		  ,@(make-inc*
		     tmp
		     (* vsize (+ 1 ;; type tag
				 (length general-slots))))
		  ,(%make-set!
		    tmp
		    (make-opr2 :opr '+ :v2 tmp :v1 base))))
	       (values tmp #f)))
	    (else
	     (values
	      (loop-s base)
	      (* vsize
		 (+ (or index 0)
		    (cond
		     ((list-index (pa$ eq? slot-name) general-slots)
		      => (cut + 1 <>))
		     ((eq? slot-name 'tag) 0)
		     (else
		      (error "Unknown slot name of complex type :"
			     slot-name type-name))))))))))
       (vector pre base offset)))
    (make-imm
     (let1 tmp (car (compute-temp-space 1))
       (make-seq
	:es
	(list
	 (%make-set! tmp (loop-s v))
	 (%make-set!
	  tmp (make-opr2
	       :opr 'sal :v1 tmp
	       :v2 (make-asm-int (cunit:imm-type-tag-size-of e))))
	 (%make-set!
	  tmp (make-opr2
	     :opr '+ :v1 tmp :v2
	     (make-asm-int
	      (hash-table-get*
	       (cunit:imm-type->tag-of e)
	       type-name
	       (error "Unknown immediate type :" type-name)))))
	 tmp))))
    (imm-ref
     (make-opr2
      :opr 'sar :v1 (loop-s v)
      :v2 (make-asm-int (cunit:imm-type-tag-size-of e)))))))

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
	  (if foregin?
	    name
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
		(hash-table-put! lbl->gas-symbol id x))))))))
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
	(opr1
	 (case opr
	   ((-) (insn*: 'neg (loop-s v)))
	   (else (error "Unknown operator of opr1 :" *self*))))
	(set!
	 (define sopr2
	   (alist->hash-table
	    '((+ . add) (- . sub) (* . imul) (/ . div)
	      (sar sar) (sal sal))
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
	      (((cut (make-misc-immediate) <> #f))
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