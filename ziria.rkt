#lang racket
(require redex)

(provide Z types Zv Zred Zmach)

(define-language Z
  [e c ::= k
           x
           (unop e)
           (binop e e)
           (if e e e)
           (let x e e)
           (letfun f (→ ((x : ρ) ...) σ) e e)
           (f e ...)
           (letref x e e)
           (deref x)
           (set x e)
           (return e)
           (bind x e e)
           (seq e e)
           take
           (emit e)
           (repeat e)
           (par e e)]
  [k ::= ()
         true
         false
         number]
  [unop ::= -]
  [binop ::= !=
             =
             <
             +
             -
             *
             div]
  [f x ::= variable-not-otherwise-mentioned]
  [α β γ ν τ ::= ()
                 bool
                 int]
  [ω (C τ)
     T]
  [μ (ST ω τ τ)]
  [ρ ::= τ
         (ref τ)]
  [σ ::= τ
         μ]
  [φ ::= ρ
         (→ (ρ ...) σ)]
  [Γ ::= ((x φ) ...)]
  [θ ::= τ
         (ref τ)
         μ
         (→ (ρ ...) σ)])

(define-metafunction Z
  lookup : x ((x any) ...) -> any or #f
  [(lookup x ())                            #f]
  [(lookup x ((x any)     (x_1 any_1) ...)) any]
  [(lookup x ((x_1 any_1) (x_2 any_2) ...)) (lookup x ((x_2 any_2) ...))])

(define-metafunction Z
  extend : x any ((x any) ...) -> ((x any) ...)
  [(extend x any ((x_1 any_1) ...)) ((x any) ,@(filter (lambda (bind) (not (eq? (car bind) (term x)))) (term ((x_1 any_1) ...))))])

(define-metafunction Z
  extends : ((x any) ...) ((x any) ...) -> ((x any) ...)
  [(extends ((x any) ...) ((x_1 any_1) ...)) ((x any) ... ,@(filter (lambda (bind) (not (member (car bind) (term (x ...))))) (term ((x_1 any_1) ...))))])

;;
;; All free ref vars used by an expression
;;
(define-metafunction Z
  ref-vars : e -> (x ...)
  [(ref-vars k)
   ()]
  [(ref-vars x)
   ()]
  [(ref-vars (unop e)) 
   (ref-vars e)]
  [(ref-vars (binop e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))]
  [(ref-vars (if e_1 e_2 e_3))
   (∪ (ref-vars e_1) (ref-vars e_2) (ref-vars e_3))]
  [(ref-vars (let x e_1 e_2))
   (∪ (ref-vars e_1) (- (ref-vars e_2) (x)))]
  [(ref-vars (letfun f (→ ((x : ρ) ...) σ) e_1 e_2))
   (∪ (diff (ref-vars e_1) (x...)) (diff (ref-vars e_2) (f)))]
  [(ref-vars (f e ...))
   (∪ (f) (ref-vars e) ...)]
  [(ref-vars (letref x e_1 e_2))
   (∪ (ref-vars e_1) (diff (ref-vars e_2) (x)))]
  [(ref-vars (deref x))
   (x)]
  [(ref-vars (set x e))
   (∪ (ref-vars e) (x))]
  [(ref-vars (return e))
   (ref-vars e)]
  [(ref-vars (bind x e_1 e_2))
   (∪ (ref-vars e_1) (diff (ref-vars e_2) (x)))]
  [(ref-vars (seq e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))]
  [(ref-vars take)
   ()]
  [(ref-vars (emit e))
   (ref-vars e)]
  [(ref-vars (repeat e))
   (ref-vars e)]
  [(ref-vars (par e_1 e_2))
   (∪ (ref-vars e_1) (ref-vars e_2))])

;;
;; Set union
;;
(define-metafunction Z
  ∪ : (x ...) ... -> (x ...)
  [(∪ (x_1 ...) (x_2 ...) (x_3 ...) ...) (∪ (x_1 ... x_2 ...) (x_3 ...) ...)]
  [(∪ (x_1 ...)) ,(remove-duplicates (term (x_1 ...)))]
  [(∪) ()])

;;
;; Set intersection
;;
(define-metafunction Z
  ∩ : (x ...) (x ...) -> (x ...)
  [(∩ (x_1 ...) (x_2 ...)) ,(filter (lambda (x) (member x (term (x_1 ...)))) (term (x_2 ...)))]
  [(∩) ()])

;;
;; Set difference
;;
(define-metafunction Z
  diff : (x ...) (x ...) -> (x ...)
  [(diff (x ...) ()) (x ...)]
  [(diff (x_1 ... x_2 x_3 ...) (x_2 x_4 ...))
   (diff (x_1 ... x_3 ...) (x_2 x_4 ...))
   (side-condition (not (memq (term x_2) (term (x_3 ...)))))]
  [(diff (x_1 ...) (x_2 x_3 ...))
   (diff (x_1 ...) (x_3 ...))])

;;
;; Set membership
;;
(define-metafunction Z
  ∈ : x (x ...) -> #t or #f
  [(∈ x   ())          #f]
  [(∈ x_1 (x_1 x ...)) #t]
  [(∈ x_1 (x_2 x ...)) (∈ x_1 (x ...))])

;;
;; Set deletion
;;
(define-metafunction Z
  delete : x (x ...) -> (x ...)
  [(delete x   ())          ()]
  [(delete x_1 (x_1 x ...)) (delete x_1 (x ...))]
  [(delete x_1 (x_2 x ...)) (x_2 x_3 ...)
                            (where (x_3 ...) (delete x_1 (x ...)))])

(define-judgment-form
  Z
  #:mode (base-type O)
  #:contract (base-type τ)
  
  [----------------
   (base-type ())]
  
  [----------------
   (base-type bool)]
  
  [---------------
   (base-type int)])

(define-judgment-form
  Z
  #:mode (types I I O)
  #:contract (types Γ e θ)
  
  ;;
  ;; Base language rules
  ;;
  
  [----------------- "T-Unit"
   (types Γ () ())]
  
  [------------------- "T-True"
   (types Γ true bool)]
  
  [-------------------- "T-False"
   (types Γ false bool)]
  
  [-------------------- "T-Int"
   (types Γ number int)]
  
  [(where θ (lookup x Γ))
   ---------------------- "T-Var"
   (types Γ x θ)]
  
  [(types Γ e_1 θ_1)
   (where (θ_1 θ_2) (unop-type unop))
   ---------------------------------- "T-Unop"
   (types Γ (unop e_1) θ_2)]
  
  [(types Γ e_1 θ_1)
   (types Γ e_2 θ_2)
   (where (θ_1 θ_2 θ_3) (binop-type binop))
   ---------------------------------------- "T-Binop"
   (types Γ (binop e_1 e_2) θ_3)]
  
  [(types Γ e_1 bool)
   (types Γ e_2 θ) (types Γ e_3 θ)
   ------------------------------- "T-If"
   (types Γ (if e_1 e_2 e_3) θ)]
  
  [(types Γ e_1 τ_1)
   (types ((x τ_1) . Γ) e_2 θ)
   --------------------------- "T-Let"
   (types Γ (let x e_1 e_2) θ)]
  
  [(types ((f (→ (ρ ...) σ)) (x ρ) ... . Γ) e_1 σ)
   (types ((f (→ (ρ ...) σ)) . Γ) e_2 θ)
   ------------------------------------------- "T-LetFun"
   (types Γ (letfun f (→ ((x : ρ) ...) σ) e_1 e_2) θ)]
  
  [(types Γ f (→ (ρ ..._1) σ))
   (types Γ e ρ) ...
   --------------------- "T-Call"
   (types Γ (f e ..._1) σ)]
  
  ;;
  ;; Computation languages rules
  ;;
  
  [(types Γ e_1 τ_1)
   (types ((x (ref τ_1)) . Γ) e_2 (ST ω α β))
   ------------------------------------------- "T-LetRef"
   (types Γ (letref x e_1 e_2) (ST ω α β))]
  
  [(types Γ x (ref τ)) (base-type α) (base-type β)
   ----------------------------------------------- "T-Deref"
   (types Γ (deref x) (ST (C τ) α β))]
  
  [(types Γ x (ref τ)) (types Γ e τ)
   (base-type α) (base-type β)
   ------------------------------------- "T-Set"
   (types Γ (set x e) (ST (C ()) α β))]
  
  [(types Γ e τ) (base-type α) (base-type β)
   ----------------------------------------- "T-Return"
   (types Γ (return e) (ST (C τ) α β))]
  
  [(types Γ c_1 (ST (C ν) α β)) (types ((x ν) . Γ) c_2 (ST ω α β))
   ----------------------------------------------------------------- "T-Bind"
  (types Γ (bind x c_1 c_2) (ST ω α β))]
  
  [(types Γ c_1 (ST (C ν) α β)) (types Γ c_2 (ST ω α β))
   ----------------------------------------------------- "T-Seq"
   (types Γ (seq c_1 c_2) (ST ω α β))]
  
  [(base-type α) (base-type β)
   ----------------------------- "T-Take"
   (types Γ take (ST (C α) α β))]
  
  [(types Γ e β) (base-type α)
   ------------------------------------ "T-Emit"
   (types Γ (emit e) (ST (C ()) α β))]
  
  [(types Γ c (ST (C ()) α β))
   ------------------------------- "T-Repeat"
   (types Γ (repeat c) (ST T α β))]
  
  [(where (Γ_1 Γ_2) (split-Γ Γ c_1 c_2))
   (types Γ_1 c_1 (ST ω_1 α β)) (types Γ_2 c_2 (ST ω_2 β γ))
   (where ω_3 (join ω_1 ω_2))
   ----------------------------------------------------------- "T-Par"
   (types Γ (par c_1 c_2) (ST ω_3 α γ))])

(define-metafunction Z
  unop-type : unop -> (θ θ)
  [(unop-type -) (int int)])

(define-metafunction Z
  binop-type : binop -> (θ θ θ)
  [(binop-type =)   (int int bool)]
  [(binop-type !=)  (int int bool)]
  [(binop-type <)   (int int bool)]
  [(binop-type +)   (int int int)]
  [(binop-type -)   (int int int)]
  [(binop-type *)   (int int int)]
  [(binop-type div) (int int int)])

(define-metafunction Z
  join : ω ω -> ω
  [(join (C ν) T) (C ν)]
  [(join T (C ν)) (C ν)]
  [(join T T)     T])

(define-metafunction Z
  split-Γ : Γ e e -> (Γ Γ)
  [(split-Γ () e_1 e_2)
   (() ())]
  [(split-Γ ((x_1 (ref τ_1)) (x φ) ...) e_1 e_2)
   (((x_1 (ref τ_1)) . Γ_1) Γ_2)
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_1))))]
  [(split-Γ ((x_1 (ref τ_1)) (x φ) ...) e_1 e_2)
   (Γ_1 ((x_1 (ref τ_1)) . Γ_2))
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))
   (side-condition (term (∈ x_1 (ref-vars e_2))))]
  [(split-Γ ((x_1 (ref τ_1)) (x φ) ...) e_1 e_2)
   (Γ_1 Γ_2)
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))]
  [(split-Γ ((x_1 φ_1) (x φ) ...) e_1 e_2)
   (((x_1 φ_1) . Γ_1) (((x_1 φ_1) . Γ_2)))
   (where (Γ_1 Γ_2) (split-Γ ((x φ) ...) e_1 e_2))])

(define-extended-language Zv Z
  ;; Continuations
  [κ ::= halt
         (popk E κ)
         (unopk unop κ)
         (binop1k binop e κ)
         (binop2k binop v κ)
         (ifk e e κ)
         (letk x e κ)
         (argk f (venv ...) (e ...) κ)
         (letrefk x e κ)
         (setk x κ)
         (returnk κ)
         (bindk x e κ)
         (seqk e κ)
         (emitk κ)]
  ;; Locations
  [l ::= variable-not-otherwise-mentioned]
  ;; Queue locations
  [q ::= variable-not-otherwise-mentioned]
  ;; Values
  [v ::= k]
  ;; Environment values. These are either values or locations.
  [venv ::= v
            l]
  ;; Store values. These are either values or closures.
  [vsto ::= v
            clo]
  ;; Closures
  [clo ::= ((x ...) e E)]
  ;; Environment
  [E ::= ((x venv) ...)]
  ;; Store
  [Σ ::= ((l vsto) ...)]
  ;; Actions
  [δ ::= tick
         wait
         (cons v)
         (yield v)]
  ;; Threads
  [t ::= (thread E Σ e κ δ)]
  ;; Queues
  [Q I O ::= (queue v ...)]
  ;; Process
  [p ::= (proc t q_1 q_2)]
  ;; Queue heap
  [Φ ::= ((q Q) ...)]
  ;; Queue wait set
  [X ::= (q ...)]
  ;; Machines
  [m ::= (mach Φ X (p ...))]
  )

(define Zred
  (reduction-relation
   Zv
   #:domain t
   [--> (thread E Σ x κ tick)
        (thread E Σ v κ tick)
        (where v (lookup x E))
        "E-Var"]
   
   [--> (thread E Σ (unop e) κ              tick)
        (thread E Σ e        (unopk unop κ) tick)
        "E-Unop"]
   
   [--> (thread E Σ (binop e_1 e_2) κ                    tick)
        (thread E Σ e_1            (binop1k binop e_2 κ) tick)
        "E-Binop"]
   
   [--> (thread E Σ (if e_1 e_2 e_3) κ               tick)
        (thread E Σ e_1              (ifk e_2 e_3 κ) tick)
        "E-If"]
   
   [--> (thread E Σ (let x e_1 e_2) κ              tick)
        (thread E Σ e_1             (letk x e_2 κ) tick)
        "E-Let"]

   [--> (thread E_1 Σ_1 (letfun f (→ ((x : ρ) ...) σ) e_1 e_2) κ            tick)
        (thread E_2 Σ_2 e_2                                    (popk E_1 κ) tick)
        (where l   ,(variable-not-in (term Σ_1) 'l))
        (where E_2 (extend f l E_1))
        (where Σ_2 (extend l ((x ...) e_1 E_2) Σ_1))
        "E-LetFun"]
   
   [--> (thread E Σ (f e_1 e_2 ...) κ                       tick)
        (thread E Σ e_1             (argk f () (e_2 ...) κ) tick)
        "E-Call"]
   
   [--> (thread E Σ (letref x e_1 e_2) κ                 tick)
        (thread E Σ e_1                (letrefk x e_2 κ) tick)
        "E-LetRef"]
   
   [--> (thread E Σ (deref x)  κ tick)
        (thread E Σ (return v) κ tick)
        (where l (lookup x E))
        (where v (lookup l Σ))
        "E-Deref"]
   
   [--> (thread E Σ (set x e) κ          tick)
        (thread E Σ e         (setk x κ) tick)
        "E-Set"]
   
   [--> (thread E Σ (return e) κ           tick)
        (thread E Σ e          (returnk κ) tick)
        (side-condition (not (redex-match Zv v (term e))))
        "E-Return"]
   
   [--> (thread E Σ (bind x e_1 e_2) κ               tick)
        (thread E Σ e_1              (bindk x e_2 κ) tick)
        "E-Bind"]
   
   [--> (thread E Σ (seq e_1 e_2) κ            tick)
        (thread E Σ e_1           (seqk e_2 κ) tick)
        "E-Seq"]
   
   [--> (thread E Σ take κ tick)
        (thread E Σ take κ wait)
        "E-TakeWait"]
   
   [--> (thread E Σ take       κ (cons v))
        (thread E Σ (return v) κ tick)
        "E-TakeConsume"]
   
   [--> (thread E Σ (emit e) κ         tick)
        (thread E Σ e        (emitk κ) tick)
        "E-Emit"]
   
   [--> (thread E Σ (repeat e)         κ tick)
        (thread E Σ (seq e (repeat e)) κ tick)
        "E-Repeat"]
   
   [--> (thread _ Σ v (popk E κ) tick)
        (thread E Σ v κ          tick)
        "E-PopK"]
   
   [--> (thread _ Σ (return v) (popk E κ) tick)
        (thread E Σ (return v) κ          tick)
        "E-PopReturnK"]
   
   [--> (thread E Σ v                  (unopk unop κ) tick)
        (thread E Σ (meta-unop unop v) κ              tick)
        "E-UnopK"]
   
   [--> (thread E Σ v (binop1k binop e κ)      tick)
        (thread E Σ e (binop2k binop v κ) tick)
        "E-Binop1K"]
   
   [--> (thread E Σ v_2                        (binop2k binop v_1 κ) tick)
        (thread E Σ (meta-binop binop v_1 v_2) κ                     tick)
        "E-Binop2K"]
   
   [--> (thread E Σ true (ifk e_1 e_2 κ) tick)
        (thread E Σ e_1  κ               tick)
        "E-IfTrueK"]
   
   [--> (thread E Σ false (ifk e_1 e_2 κ) tick)
        (thread E Σ e_2   κ               tick)
        "E-IfFalseK"]
   
   [--> (thread E_1 Σ v (letk x e κ) tick)
        (thread E_2 Σ e (popk E_1 κ) tick)
        (where E_2 (extend x v E_1))
        "E-LetK"]
   
   [--> (thread E Σ v_2 (argk f (venv_1 ...)     (e_1 e_2 ...) κ) tick)
        (thread E Σ e_1 (argk f (venv_1 ... v_2) (e_2 ...) κ)     tick)
        "E-ArgK"]
   
   [--> (thread E Σ x   (argk f (venv_1 ...)   (e_1 e_2 ...) κ) tick)
        (thread E Σ e_1 (argk f (venv_1 ... l) (e_2 ...) κ)     tick)
        (where l (lookup x E))
        "E-RefArgK"]
   
   [--> (thread E_1 Σ v_2 (argk f (venv_1 ...) () κ) tick)
        (thread E_2 Σ e_f (popk E_1 κ)            tick)
        (where (venv ..._1)        (venv_1 ... v_2))
        (where l_f                 (lookup f E_1))
        (where ((x ..._1) e_f E_f) (lookup l_f Σ))
        (where E_2 (extends ((x venv) ...) E_f))
        "E-CallK"]

   [--> (thread E_1 Σ x_2 (argk f (venv_1 ...) () κ) tick)
        (thread E_2 Σ e_f (popk E_1 κ)            tick)
        (where l                   (lookup x_2 E_1))
        (where (venv ..._1)        (venv_1 ... l))
        (where l_f                 (lookup f E_1))
        (where ((x ..._1) e_f E_f) (lookup l_f Σ))
        (where E_2 (extends ((x venv) ...) E_f))
        "E-CallRefK"]
   
   [--> (thread E_1 Σ_1 v (letrefk x e κ) tick)
        (thread E_2 Σ_2 e (popk E_1 κ)   tick)
        (where l   ,(variable-not-in (term Σ_1) 'l))
        (where E_2 (extend x l E_1))
        (where Σ_2 (extend l v Σ_1))
        "E-LetRefK"]
   
   [--> (thread E Σ_1 v           (setk x κ) tick)
        (thread E Σ_2 (return ()) κ          tick)
        (where l   (lookup x E))
        (where Σ_2 (extend l v Σ_1))
        "E-SetK"]
   
   [--> (thread E Σ v          (returnk κ) tick)
        (thread E Σ (return v) κ           tick)
        "E-ReturnK"]
   
   [--> (thread E_1 Σ (return v) (bindk x e κ) tick)
        (thread E_2 Σ e          (popk E_1 κ)  tick)
        (where E_2 (extend x v E_1))
        "E-BindK"]
   
   [--> (thread E Σ (return v) (seqk e κ) tick)
        (thread E Σ e          κ          tick)
        "E-SeqK"]
   
   [--> (thread E Σ v           (emitk κ) tick)
        (thread E Σ (return ()) κ         (yield v))
        "E-EmitK"]))

(define (replicate n x)
  (if (= n 0)
      null
      (cons x (replicate (- n 1) x))))

(define-metafunction Zv
  [(meta-unop - number) ,(apply - (term (number)))])

(define-metafunction Zv
  [(meta-binop =   number   number)   true]
  [(meta-binop =   number_1 number_2) false]
  [(meta-binop !=  number   number)   false]
  [(meta-binop !=  number_1 number_2) true]
  [(meta-binop <   number_1 number_2) ,(if (apply < (term (number_1 number_2))) (term true) (term false))]
  [(meta-binop +   number_1 number_2) ,(apply + (term (number_1 number_2)))]
  [(meta-binop -   number_1 number_2) ,(apply - (term (number_1 number_2)))]
  [(meta-binop *   number_1 number_2) ,(apply * (term (number_1 number_2)))]
  [(meta-binop div number_1 number_2) ,(apply quotient (term (number_1 number_2)))])

(define-judgment-form
  Zv
  #:mode (→z I O)
  #:contract (→z t t)
  
  [(where (t_1 ... t t_2 ...) ,(apply-reduction-relation Zred (term (thread E Σ e κ δ))))
   --------------------------------------------------------------------------------------
   (→z (thread E Σ e κ δ) t)])

(define Zmach
  (reduction-relation
   Zv
   #:domain m
   [--> (mach Φ X (p_1 ... (proc (thread E_1 Σ_1 e_1 κ_1 δ_1) q_1 q_2) p_2 ...))
        (mach Φ X (p_1 ... (proc (thread E_2 Σ_2 e_2 κ_2 δ_2) q_1 q_2) p_2 ...))
        (judgment-holds (→z (thread E_1 Σ_1 e_1 κ_1 δ_1) (thread E_2 Σ_2 e_2 κ_2 δ_2)))
        "P-Thread"]
   
   [--> (mach Φ X_1 (p_1 ... (proc (thread E Σ e κ wait) q_1 q_2) p_2 ...))
        (mach Φ X_2 (p_1 ... (proc (thread E Σ e κ wait) q_1 q_2) p_2 ...))
        (where #f       (dequeue Φ q_1))
        (side-condition (or (term (∈ q_2 X_1)) (term (isout Φ q_2))))
        (side-condition (not (term (∈ q_1 X_1))))
        (where (q ...)  X_1)
        (where X_2      (q_1 q ...))
        "P-Wait"]
   
   [--> (mach Φ_1 X (p_1 ... (proc (thread E Σ e κ wait)     q_1 q_2) p_2 ...))
        (mach Φ_2 X (p_1 ... (proc (thread E Σ e κ (cons v)) q_1 q_2) p_2 ...))
        (side-condition (or (term (∈ q_2 X)) (term (isout Φ_1 q_2))))
        (where (Φ_2 v) (dequeue Φ_1 q_1))
        "P-Consume"]
   
   [--> (mach Φ_1 X_1 (p_1 ... (proc (thread E Σ e κ (yield v)) q_1 q_2) p_2 ...))
        (mach Φ_2 X_2 (p_1 ... (proc (thread E Σ e κ tick)      q_1 q_2) p_2 ...))
        (where X_2 (delete q_2 X_1))
        (where Φ_2 (enqueue Φ_1 q_2 v))
        "P-Yield"]
   
   [--> (mach ((q Q) ...)                 X (p_1 ... (proc (thread E Σ (par e_1 e_2) κ tick) q_1 q_2) p_2 ...))
        (mach ((q_new (queue)) (q Q) ...) X (p_1 ... (proc (thread E Σ e_1 κ tick) q_1 q_new) (proc (thread E Σ e_2 κ tick) q_new q_2) p_2 ...))
        (fresh q_new)
        "P-Spawn"]))

(define-metafunction Zv
  isout : Φ q -> #t or #f
  [(isout (_ ... (q _)) q) #t]
  [(isout _ _) #f])

(define-metafunction Zv
  dequeue : Φ q -> (Φ v) or #f
  [(dequeue ((q_1 Q_1) ... (q (queue v_1 v ...)) (q_2 Q_2) ...) q) (((q_1 Q_1) ... (q (queue v ...)) (q_2 Q_2) ...) v_1)]
  [(dequeue Φ q) #f])

(define-metafunction Zv
  enqueue : Φ q v -> Φ or #f
  [(enqueue ((q_1 Q_1) ... (q (queue v_1 ...)) (q_2 Q_2) ...) q v) ((q_1 Q_1) ... (q (queue v_1 ... v)) (q_2 Q_2) ...)]
  [(enqueue Φ q v) #f])

;;
;; A simple macro to catch exceptions thrown by the error function
;;
(define-syntax try
  (syntax-rules ()
    [(_ body) (with-handlers ([exn:fail? (lambda (exn)
                                           (displayln (exn-message exn))
                                           #f)])
                body)]))
