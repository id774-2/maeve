(define-module maeve.compiler.arch
 (use gauche.parameter)
 (use maeve.lib.gauche.macro-util)
 (export-all))

(select-module maeve.compiler.arch)

(mac
 `(begin
    ,@(map
       (lambda (n)
	 `(define ,n (make-parameter "parameterized-arch is not installed.")))
       '(variable-size registers num-of-registers special-registers
		       stack-pointer frame-pointer arch make-call-c-function
		       make-misc-immidiate))))

(define x86-64:make-call-c-function "make-call-c-function not initialized.")
(define x86-32:make-call-c-function "make-call-c-function not initialized.")

(define (x86-64:make-misc-immidiate x . opt-default)
  ;; #define SCM__MAKE_ITAG(num)  (((num)<<4) + 6)
  (define (%make num)
    (+ 6 (ash num 4)))
  (case x
    ;; #define SCM_FALSE           SCM_OBJ(SCM__MAKE_ITAG(0)) /* #f */
    ;; #define SCM_TRUE            SCM_OBJ(SCM__MAKE_ITAG(1)) /* #t  */
    ;; #define SCM_NIL             SCM_OBJ(SCM__MAKE_ITAG(2)) /* '() */
    ;; #define SCM_EOF             SCM_OBJ(SCM__MAKE_ITAG(3)) /* eof-object */
    ;; #define SCM_UNDEFINED       SCM_OBJ(SCM__MAKE_ITAG(4)) /* #undefined */
    ;; #define SCM_UNBOUND         SCM_OBJ(SCM__MAKE_ITAG(5)) /* unbound value */
    ((#f false)      (%make 0))
    ((#t true)       (%make 1))
    ((() nil null)   (%make 2))
    ((eof)           (%make 3))
    ((undef)         (%make 4))
    ((unbound)       (%make 5))
    (else
     (cond
      ((pair? opt-default) (car opt-default))
      (else
       (error "Bad misc immidiate tag :" x))))))

(define (compile-for-x86-64 thunk)
  (let1 regs '#(rax rbx rcx rdx rsi rdi r8 r9 r10 r11 r12 r13 r14 r15)
    (parameterize
	((arch 'x86-64)
	 (variable-size 8)
	 (registers regs)
	 (num-of-registers (vector-length regs))
	 (special-registers '#(rsp rbp))
	 (stack-pointer 'rsp)
	 (frame-pointer 'rbp)
	 (make-call-c-function x86-64:make-call-c-function)
	 (make-misc-immidiate  x86-64:make-misc-immidiate))
      (thunk))))


(define (compile-for-x86-32 thunk)
  (let1 regs '#(eax ebx ecx edx esi edi)
    (parameterize
	((arch 'x86-32)
	 (variable-size 4)
	 (registers regs)
	 (num-of-registers (vector-length regs))
	 (special-registers '#(esp ebp))
	 (stack-pointer 'esp)
	 (frame-pointer 'ebp)
	 (make-call-c-function x86-32:make-call-c-function)
	 (make-misc-immidiate  x86-64:make-misc-immidiate))
      (thunk))))

(provide "maeve/compiler/arch")
