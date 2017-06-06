#lang racket
(require redex)

(require "ziria.rkt")

;;
;; A few simple typing judgment tests
;;
(test-equal
 (judgment-holds
  (types () 1 τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types ((x int)) x τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types () (+ 1 3) τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types () (- 1) τ)
  τ)
 (list (term int)))

(test-equal
 (judgment-holds
  (types ((x (ref int))) x θ)
  θ)
 (list (term (ref int))))

(test-equal
 (judgment-holds
  (types ((x (ref int))) (set x (+ 3 4)) (ST (C ()) int int)))
 #t)

;;
;; Testing the thread reduction relation
;;

;; Test that e1 evaluates to e2 in the given environment and store.
(define (test-eval-exp E Σ e1 e2)
  (define (thread-exp-matches t)
    (match t
      [`(thread ,_ ,_ ,e halt tick) (eq? e e2)]
      [_ #f]))
  (test-->>∃
   Zred
   (term (thread ,E ,Σ ,e1 halt tick))
   thread-exp-matches))

;; Trace reduction of e1 in given environment and store.
(define (trace-zred E Σ e1)
  (traces
   Zred
   (term (thread ,E ,Σ ,e1 halt tick))))

(test-eval-exp '() '()
               (term (if (= 10 (+ 9 1)) (+ 1 10) (- 19)))
               11)

(test-eval-exp '((x 3)) '()
               (term (if (= x 3) 1 0))
               1)

(test-eval-exp '() '()
               (term (let x (+ 1 2) (+ x x)))
               6)

(test-eval-exp '() '()
               (term (letfun plus (→ ((x : int) (y : int)) int) (+ x y) (plus 1 2)))
               3)

(test-eval-exp '() '()
               (term (letfun fact (→ ((x : int)) int) (if (< x 2) 1 (* x (fact (- x 1)))) (fact 4)))
               24)

;;
;; Testing the machine reduction rule
;;

(define-syntax do
  (syntax-rules (let letref letfun <- >>>)
    [(_ let x e rest ...) (term (let x e ,(do rest ...)))]
    [(_ letref x e rest ...) (term (letref x e ,(do rest ...)))]
    [(_ letfun f args e rest ...) (term (letfun f args e ,(do rest ...)))]
    [(_ e) (term e)]
    [(_ e1 >>> e2) (term (par ,e1 ,e2))]
    [(_ v <- e rest ...)
     (term (bind v ,(do e) ,(do rest ...)))]
    [(_ e rest ...)
     (term (seq e ,(do rest ...)))]
    [(_ return e)
     (term (return e))]))

;;
;; Convert a Ziria expression and input into an initial machine configuration
;;
(define (exp->mach e in)
  (term (mach ((q_1 (queue ,@in)) (q_2 (queue))) () ((proc (thread () () ,e halt tick) q_1 q_2)))))

;;
;; Run a Ziria expression with given input and return all possible outputs.
;;

(define (run-ziria e in)
  (define (output m)
    (match m
      [`(mach (,_ ... (,_ (queue ,v_in ...)) (,_ (queue ,v_out ...))) ,_ ,_)
       v_out]
      [_ #f]))
  (map output
       (apply-reduction-relation* Zmach
                                  (exp->mach e in)
                                  #:cache-all? #t)))


;;
;; Test that running a Ziria expression with a given intput yields the specified output
;;
(define (test-exists e in out)
  (define (mach-output-matches? m)
    (match m
      [`(mach (,_ ... (,_ (queue ,v ...))) ,_ ,_) (equal? out v)]
      [_ #f]))
  (test-->>∃
   Zmach
   (exp->mach e in)
   mach-output-matches?))

;;
;; Test that running a Ziria expression with a given intput reduces to a final
;; state with the specified final input and output
;;
(define (test-final e in in-fin out-fin)
  (define (mach-in-out-matches? m)
    (match m
      [`(mach (,_ ... (,_ (queue ,v_in ...)) (,_ (queue ,v_out ...))) ,_ ,_)
       (and (equal? in-fin  v_in)
            (equal? out-fin v_out))]
      [_ #f]))
  (for-each (lambda (m) (test-predicate mach-in-out-matches? m))
            (apply-reduction-relation* Zmach
                                       (exp->mach e in)
                                       #:cache-all? #t)))

(define pipe
  (term (repeat ,(do x <- take
                     (emit x)))))

;; Trace the evaluation of pipe

;(traces Zmach (exp->mach pipe '(1 2)))

(define (zmap f)
  (term (repeat ,(do x <- take
                     (emit (,f x))))))

;; Trace evaluation of map

;(traces Zmach (exp->mach (do letfun f (→ ((x : int)) int) (+ x 1)
;                             ,(zmap 'f))
;                         '(1 2)))

(test-final (do letfun f (→ ((x : int)) int) (+ x 1)
                ,(zmap 'f))
             '(1 2 3 4 5)
             '()
             '(2 3 4 5 6))

;;
;; A well-typed term since we can split the heap
;;
(define split-heap-test
  (do letref x 0
      (term (repeat ,(do z1 <- (deref x)
                         z2 <- take
                         (emit z1)
                         (emit z2)
                         (set x (+ z1 z2)))))
      >>>
      (term (repeat ,(do z <- take
                         (emit z))))))

(test-equal
 (judgment-holds
  (types () ,split-heap-test (ST T int int)))
 #t)

(test-final split-heap-test
             '(1 2)
             '()
             '(0 1 1 2))

;;
;; Not a well-typed term since we *cannot* split the heap
;;
(define split-heap-test2
  (do letref x 0
      (term (repeat ,(do z1 <- (deref x)
                         z2 <- take
                         (emit z1)
                         (emit z2)
                         (set x (+ z1 z2)))))
      >>>
      (do z <- take
          (set x z)
          (emit z))))

(test-equal
 (judgment-holds
  (types () ,split-heap-test2 θ) θ)
 '())

;;
;; Should only consume 1 datum from input queue
;;
(define test-not-eager
  (do pipe
      >>>
      (do x <- take
          (emit x))))

(test-final test-not-eager
             '(1 2 3)
             '(2 3)
             '(1))

;;
;; Test references
;;
(define test-refs
  (do letref x 1
      (repeat ,(do y <- take
                   z <- (deref x)
                   (set x (+ y z))
                   t <- (deref x)
                   (emit t)))))

(test-equal
 (judgment-holds
  (types () ,test-refs θ) θ)
 '((ST T int int)))

(test-final test-refs
             '(1 2 3 4 5)
             '()
             '(2 4 7 11 16))

(define test-ref-args
  (do letref x 1
      letfun setref (→ ((r : (ref int)) (x : int)) (ST (C ()) int int)) (set r x)
      (repeat ,(do y <- take
                   z <- (deref x)
                   (setref x (+ y z))
                   t <- (deref x)
                   (emit t)))))

(test-equal
 (judgment-holds
  (types () ,test-ref-args θ) θ)
 '((ST T int int)))

(test-final test-ref-args
             '(1 2 3 4 5)
             '()
             '(2 4 7 11 16))

(define test-final-ref-arg
  (do letref x 1
      letfun setref (→ ((x : int) (r : (ref int))) (ST (C ()) int int)) (set r x)
      (repeat ,(do y <- take
                   z <- (deref x)
                   (setref (+ y z) x)
                   t <- (deref x)
                   (emit t)))))
(test-equal
 (judgment-holds
  (types () ,test-final-ref-arg θ) θ)
 '((ST T int int)))

(test-final test-final-ref-arg
             '(1 2 3 4 5)
             '()
             '(2 4 7 11 16))

;;
;; Test recursive function
;;

(define test-fib
  (do letfun fib (→ ((n : int)) int) (if (= n 0)
                                         0
                                         (if (= n 1)
                                             1
                                             (+ (fib (- n 1)) (fib (- n 2)))))
      (repeat ,(do n <- take
                   (emit (fib n))))))

(test-equal
 (judgment-holds
  (types () ,test-fib θ) θ)
 '((ST T int int)))

(test-final test-fib
             '(1 2 3 4 5 6 7)
             '()
             '(1 1 2 3 5 8 13))

