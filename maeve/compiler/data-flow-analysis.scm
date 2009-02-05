(define-module maeve.compiler.data-flow-analysis
  (use maeve.compiler.intermediate-language-util)
  (use maeve.compiler.intermediate-language-instance)
  (export-all))

(select-module maeve.compiler.data-flow-analysis)

(define-macro (%dump ht)
  `(hash-table-dump*
    ,ht :pre-key-filter il:id
    :pre-value-filter
    (lambda (xs)
      (map (lambda (x) (il:id x)) xs))))

(define (compute-pred&succ:medium e)
  (define (hash-table-filter-push! ht k v)
    (when (and k v) (hash-table-push! ht k v)))
  (let ((pred (make-hash-table 'eqv?))
	(succ (make-hash-table 'eqv?))
	(stm-pred (make-hash-table 'eqv?))
	(stm-succ (make-hash-table 'eqv?))
	(id->block (make-hash-table 'eqv?))
	(tail-blocks '()))
    (define (block-addr->block b)
      (hash-table-get id->block (block-addr:name-of* b) #f))
    (mir-traverse
     (target e) (type no-update)
     (use-circular-graph?)
     (handler
      (block
       (hash-table-put! id->block id *self*)
       (unless (or default-succ opt-succ)
	 (push! *self* tail-blocks))
       (*next-handler*))))
    (hash-table-for-each
     id->block
     (lambda (_ b)
       (for-each
	(lambda (s)
	  (hash-table-put! stm-succ s '())
	  (hash-table-put! stm-pred s '()))
	(block:es-of* b))
       (hash-table-put! succ b '())
       (hash-table-put! pred b '())))
    (hash-table-for-each
     id->block
     (lambda (_ b)
       (decompose-block b)
       (let ((s0 (block-addr->block default-succ))
	     (s1 (block-addr->block opt-succ)))
	 (pair-fold
	  (lambda (s _)
	    (define (find-next-block b)
	      (let loop ((b b))
		(insert-code
		 (block? b)
		 (let-decompose-block
		  b
		  (cond
		   ((pair? es) (list (car es)))
		   (else
		    (append
		     (loop (block-addr->block default-succ))
		     (loop (block-addr->block opt-succ)))))))))
	    (let ((pre (car s))
		  (posts
		   (if (null? (cdr s))
		     (append
		      (find-next-block s0)
		      (find-next-block s1))
		     (list (cadr s)))))
	      (for-each
	       (lambda (post)
		 (hash-table-filter-push! stm-pred post pre)
		 (hash-table-filter-push! stm-succ pre  post))
	       posts)))
	  #f (append es (insert-code* test test)))
	 (hash-table-filter-push! succ  b s0)
	 (hash-table-filter-push! succ  b s1)
	 (hash-table-filter-push! pred s0  b)
	 (hash-table-filter-push! pred s1  b))))
    ;; (%dump pred) (%dump stm-pred) (%dump succ) (%dump stm-succ)
    (make-compute-pred&succ-result
     :pred pred :succ succ :stm-succ stm-succ :stm-pred stm-pred
     :tail-blocks tail-blocks :id->block id->block)))


(define (bit-vector-for-each proc bit-vec)
  (ultra-iterator () () proc () (:bit-vector bit-vec)))

(define (bit-vector-map->list proc bit-vec)
  (ultra-iterator () (<list>) proc () (:bit-vector bit-vec)))

(define (bit-vector-map->bit-vector proc bit-vec)
  (ultra-iterator () (:bit-vector) proc () (:bit-vector bit-vec)))

(define-macro (define-df-analysis name loop-eq-fn eq-fns exp)
  (with-gensyms
   (e x p k ht result changed? new old)
   (define set-operations
     '(("isec" . lset-intersection)
       ("union" . lset-union)
       ("adjoin" . lset-adjoin)
       ("diff" . lset-difference)))
   (define set-operator-regexp
     (string->regexp
      (tree->string
       (list
	"^\\*("
	(intersperse "|" (map car set-operations))
	")-([0-9]+?)\\*$"))))
   (define fold-set-operator-regexp
     (string->regexp
      (tree->string
       (list
	"^\\*fold-("
	(intersperse "|" (map car set-operations))
	")-([0-9]+?)\\*$"))))
   (define (dispatch-operation rx)
     (list
      (assoc-ref
       set-operations (rxmatch-substring rx 1))
      (list-ref
       eq-fns (string->number (rxmatch-substring rx 2)))))
   `(define (,name ,e)
      (decompose-compute-pred&succ-result (compute-pred&succ:medium ,e))
      ,(match-map-tree-pre-order2
	(target exp)
	(loop-sym loop)
	(handler
	 (((= (compose set-operator-regexp x->string)
	      (? regmatch? rx))
	   xs ...)
	  `,(append (dispatch-operation rx) (map loop xs)))
	 (('*loop&copy* x)
	  `(map il:copy ,(loop `(*loop* ,x))))
	 (('*loop* x)
	  `(hash-table-get ,result ,x '()))
	 (((= (compose fold-set-operator-regexp x->string)
	      (? regmatch? rx)) proc xs)
	  `(fold
	    (lambda (,x ,p)
	      (,@(dispatch-operation rx) ,p ,(loop `(,proc ,x))))
	    '() ,xs))
	 (('*dfe*
	   (v ((? (cut memq <> '(succ pred stm-pred stm-succ)) type) u)) exp)
	  `(rlet1
	    ,result (make-hash-table 'eqv?)
	    (define ,changed? #t)
	    (while ,changed?
	      (set! ,changed? #f)
	      (hash-table-for-each
	       ,type
	       (lambda (,u ,v)
		 (hash-table-update!
		  ,result ,u
		  (lambda (,old)
		    (rlet1
		     ,new  ,(loop exp)
		     (unless (lset= ,loop-eq-fn ,old ,new)
		       (set! ,changed? #t))))
		  '()))))))
	 mmt:default)))))

(define (%def x)
  (case/pred
   x
   (set!?
    (let-decompose-set!
     x (list (make-rd-elm :dist dist :src src :num 0))))
   (set!-vls?
    (let-decompose-set!-vls
     x (map1-with-index
	(lambda (i d) (make-rd-elm :dist d :src src :num i))
	dists)))
   (else '())))

(define (rd-elm:interfere? x y)
  (cond
   ((and (rd-elm? x) (rd-elm? y))
    (il:eqv? (rd-elm:dist-of x) (rd-elm:dist-of y)))
    
   (else (error "rd-elm:interfere? type error :" x y))))

(define-df-analysis reach
  il:equal?-without-id
  (rd-elm:interfere? il:equal?-without-id)
  (hash-table-update-all!
   (*dfe*
    (preds (stm-pred s))
    (*fold-union-1*
     (lambda (p)
       (*union-1* (%def p)
		  (*diff-0* (*loop* p) (%def p))))
     preds))
   (lambda (k x)
     (rlet1 ht (make-hash-table 'eqv?)
	    (for-each
	     (lambda (e)
	       (decompose-rd-elm e) (hash-table-push! ht dist e))
	     x)))))

(define (live-elm:interfere? x y)
  (il:eqv? (live-elm:var-of x) (live-elm:var-of y)))

(define (%use&kill x)
  (let ((uses '()) (kills '()))
    (mir-traverse
     (target x) (type no-update)
     (inherited-attr (set-dist? #f set-dist?))
     (handler
      (set! (loop-s src) (*loop* :self dist :set-dist? #t))
      (set!-vls (loop-s src)
		(for-each (*cut-loop* :self <> :set-dist? #t) dists))
      (lvar
       (define (c xs)
	 (lset-adjoin live-elm:interfere? xs (make-live-elm :var *self*)))
       (if set-dist?
	 (update! kills c)
	 (update! uses  c)))))
    (values uses kills)))

(define-df-analysis live
  il:equal?-without-id
  (live-elm:interfere?)
  (*dfe*
   (succs (stm-succ p))
   (let*-values
       (((u k) (%use&kill p))
	((olds)
	 (*diff-0* (*fold-union-0* *loop&copy* succs) k)))
     ;; (format #t "~s : ~s ~s\n" (il->sexp/ss p) (map il->sexp/ss u) (map il->sexp/ss k))
     (for-each (cut live-elm:end?-set! <> #t) (*diff-0* u olds))
     (for-each (cut live-elm:end?-set! <> #f) (*diff-0* olds u))
     ;; (format #t "~s : ~s\n" (il:id p) (map il->sexp/ss (*diff-0* u olds)))
     (*union-0* u olds))))

;; (define-df-analysis path eq? (eq?)
;;   (*dfe* (xs ((or succ pred) p))
;; 	 (apply *union-0* succs (map *loop* xs))))

;; (let1 x
;;     '#(lmd 735 (#0=#(lvar 673 m) #1=#(lvar 674 n)) (#2=#(lvar 719 #f) #3=#(lvar 703 #f) #4=#(lvar 695 #f) #5=#(lvar 689 #f) #6=#(lvar 685 #f) #7=#(lvar 679 #f)) #f (#(block 731 (#(set!-vls 720 (#2#) #(call 718 #(mem 717 #8=#(label 602 zero? #f) #f) (#0#) #f))) #(block-addr 732 729) #(block-addr 733 727) #(opr2 721 = #2# #(const 722 6))) #(block 727 (#(set!-vls 696 (#4#) #(call 694 #(mem 693 #8# #f) (#1#) #f))) #(block-addr 714 711) #(block-addr 715 709) #(opr2 697 = #4# #(const 698 6))) #(block 709 (#(set!-vls 680 (#7#) #(call 678 #(mem 676 #10=#(label 587 - #f) #f) (#0# #(const 677 1)) #f)) #(set!-vls 686 (#6#) #(call 684 #(mem 682 #10# #f) (#1# #(const 683 1)) #f)) #(call 687 #(mem 681 #11=#(label 671 ack #(mod 669 ack () (#(label 80 print-as-decimal #f) #12=#(label 590 + #f) #8# #10#) () #f)) #f) (#0# #6#) #f) #(set!-vls 690 (#5#) #(vls 837 (#(result 838 0)))) #(call 691 #(mem 675 #11# #f) (#7# #5#) #t)) #(block-addr 710 708) #f #f) #(block 711 (#(set!-vls 704 (#3#) #(call 702 #(mem 700 #10# #f) (#0# #(const 701 1)) #f)) #(call 706 #(mem 699 #11# #f) (#3# #(const 705 1)) #t)) #(block-addr 712 708) #f #f) #(block 708 () #(block-addr 728 726) #f #f) #(block 729 (#(call 725 #(mem 723 #12# #f) (#1# #(const 724 1)) #t)) #(block-addr 730 726) #f #f) #(block 726 () #f #f #f)))
;;   (hash-table-dump*
;;    (live x) :pre-key-filter il:id
;;    :value-filter (map$ (lambda (x)
;; 			 (if (live-elm:end?-of x)
;; 			   (list (live-elm:var-of x) (live-elm:end?-of x))
;; 			   (live-elm:var-of x)))))
;;   (il->graphviz* "test" x)
;;   (process-wait-any #t))

;; 0 : (set!-values (a b c) (values 1 2 3))
;; 1 : (set! c 4)
;; 2 : (set!-values (b) 5)
;; 3 : (values a b c)

;; 0 : ()
;; 1 : ((a 1) (b 2) (c 3))
;; 2 : ((a 1) (b 2) (c 4))
;; 3 : ((a 1) (b 5) (c 4))

(provide "maeve/compiler/data-flow-analysis")