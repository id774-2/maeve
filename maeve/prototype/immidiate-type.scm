
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
      (else (error "Bad misc immidiate tag :" x))))))

(define tag (cut logand #b111 <>))

(define (int? x) (= 1 (tag x)))
(define (int-value x) (ash x -2))
(define (make-int x) (+ 1 (ash x 2)))

(define	(char? x) (= (logand x #b111) 2))
(define	(char-value x) (ash x -2))
(define	(make-char x) (+ 2 (ash x 2)))

(define (immidiate? x) (= (logand x #b1111 6)))

(define (pp-binary b) (format #t "~16,' ,' ,4:b" b))
               1#<undef>
              10#<undef>
              11#<undef>


(let* ((n 100)
       (i (make-char n)))
  (print (char? i) (= n (char-value i))))

(let* ((n 100)
       (i (make-int n)))
  (print (int? i) (= n (int-value i))))

(for-each
 (lambda (x)
   (pp-binary (x86-64:make-misc-immidiate x))
   (format #t " ~10s " x)
   (newline))
 '(#f #t () eof undef unbound))
             110 #f         
          1 0110 #t         
         10 0110 ()         
         11 0110 eof        
        100 0110 undef      
        101 0110 unbound    
#<undef>
 bool
 null
 char
 fixnum
 symbol 
 eof
 undef
 unbound

(eq-hash 'aaaaaaaaaaaaaaauiuyheatuhaeuhtgareuhaerutalhaeruhla3qu4h56tqa8ytsaregthaLUDghaluthgaleuhtglaeaelrutylareuaerterastasy3qaiu4y5tliu3qy45liu423y5liu2y3lu54LIHFESUHFGVLiAGWL4IE8TW4UItluahrluthzdthaelrarleuhaleuwerluaehruWHETLUHTLAUEHRLEUALURHTALEHTALIUTAO4IU56Q3867984GUHFDGHZDGNJZNN.ZKN)
2599161820
