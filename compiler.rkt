#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
(require data/queue)
(require graph)
(require "interp.rkt")

(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
(require racket/trace)
(require "interp-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Partial evaluation for Lvar language
;; Bonus question pass
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (make-inert ex)
  (match ex
    [(Int n) (cons n '())]
    ;;[(Let x e body) (cons 0 (Let x (pe-exp e) (pe-exp body)))]
    [(Prim '+ (list ex1 ex2)) (let* ([pair_data_1 (make-inert ex1)]
                                     [pair_data_2 (make-inert ex2)]
                                     [ex3 (cdr pair_data_1)]
                                     [ex4 (cdr pair_data_2)]
                                     [n_f (fx+ (car pair_data_1) (car pair_data_2))]
                                     [exp_f (cond
                                              [(and (empty? ex3) (empty? ex4)) empty]
                                              [(empty? ex4) ex3]
                                              [(empty? ex3) ex4]
                                              [else (Prim '+ (list ex3 ex4))])])
                                (cons n_f exp_f))]
    [else (cons 0 ex)]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(exp1 exp2) (let* ([data (make-inert (Prim '+ (list exp1 exp2)))]
                        [exp_f (cdr data)]
                        [ret (cond
                               [(= 0 (car data)) exp_f]
                               [(empty? exp_f) (Int (car data))]
                               [else (Prim '+ (list (Int (car data)) (cdr data)))])])
                   ret)]))

(define (pe-sub r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx- n1 n2))]
    [(_ _) (Prim '- (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]
    [(Prim '- (list e1 e2)) (pe-sub (pe-exp e1) (pe-exp e2))]
    [(Let x e body) (Let x (pe-exp e) (pe-exp body))]))

(define (pe-Lvar p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; shrink Lvec -> Lvec
(define (shrink p)
  (match p
    ;; [(Program info e) (Program info (shrink e))]
    [(Var x) (Var x)]
    [(Int x) (Int x)]
    [(Void) (Void)]
    [(Bool x) (Bool x)]
    [(Let x rhs body) (Let x (shrink rhs) (shrink body))]
    [(If cnd e1 e2) (If (shrink cnd) (shrink e1) (shrink e2))]
    [(Prim 'and (list e1 e2)) (If (shrink e1) (shrink e2) (Bool #f))]
    [(Prim 'or (list e1 e2)) (If (shrink e1) (Bool #t) (shrink e2))]
    [(Prim op es) (Prim op (map shrink es))]
    [(Begin es body) (Begin (map shrink es) (shrink body))]
    [(SetBang var rhs) (SetBang var (shrink rhs))]
    [(WhileLoop cnd body) (WhileLoop (shrink cnd) (shrink body))]
    [(HasType exp type) (HasType (shrink exp) type)]
    ;; Lfun
    [(ProgramDefsExp info defs exp)
     (ProgramDefs info
                  (append (map shrink defs) (list (Def 'main empty 'Integer empty (shrink exp)))))]
    [(Apply fun exps) (Apply (shrink fun) (map shrink exps))]
    [(Def name params rty info body) (Def name params rty info (shrink body))]
    [else (error "Shrink unhandled case" p)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define fnames (make-hash))
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Bool b) (Bool b)]
      [(Void) (Void)]
      [(Int n) (Int n)]
      [(If e1 e2 e3) (If ((uniquify-exp env) e1) ((uniquify-exp env) e2) ((uniquify-exp env) e3))]
      [(Let x e body) (let* ([new_x (gensym x)] [new_env (dict-set env x new_x)])
                        (Let new_x ((uniquify-exp env) e) ((uniquify-exp new_env) body)))]
      [(Begin es body) (Begin (map (uniquify-exp env) es) ((uniquify-exp env) body))]
      [(SetBang var_sym rhs) (SetBang (dict-ref env var_sym) ((uniquify-exp env) rhs))]
      [(WhileLoop cnd body) (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(HasType exp type) (HasType ((uniquify-exp env) exp) type)]
      [(Prim op es) (Prim op (map (uniquify-exp env) es))]
      [(Apply fun exps) (Apply ((uniquify-exp env) fun) (map (uniquify-exp env) exps))]
      [(Def name params rty info body)
       (dict-set! fnames name (length params))
       (set! env (dict-set env name name))
       (define new_params
         (for/list ([param params])
           (define new_name (gensym (car param)))
           (set! env (dict-set env (car param) new_name))
           (cons new_name (cdr param))))
       (Def name new_params rty info ((uniquify-exp env) body))]
      [else (error "Uniquify unhandled case" e)])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(ProgramDefs info defs)
     (set! fnames (make-hash))
     (define defs2 (map (uniquify-exp '()) defs))
     ;; (define new_info (dict-set info 'fnames fnames))
     (ProgramDefs info defs2)]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (reveal_functions e)
  (match e
    [(ProgramDefs info defs) (ProgramDefs info (map reveal_functions defs))]
    [(Var x) (if (dict-ref fnames x #f) (FunRef x (dict-ref fnames x #f)) (Var x))]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(If e1 e2 e3) (If (reveal_functions e1) (reveal_functions e2) (reveal_functions e3))]
    [(Let x e body) (Let x (reveal_functions e) (reveal_functions body))]
    [(Begin es body) (Begin (map reveal_functions es) (reveal_functions body))]
    [(SetBang var_sym rhs) (SetBang var_sym (reveal_functions rhs))]
    [(WhileLoop cnd body) (WhileLoop (reveal_functions cnd) (reveal_functions body))]
    [(HasType exp type) (HasType (reveal_functions exp) type)]
    [(Prim op es) (Prim op (map reveal_functions es))]
    [(Apply fun exps) (Apply (reveal_functions fun) (map reveal_functions exps))]
    [(Def name params rty info body) (Def name params rty info (reveal_functions body))]
    [else (error "Reveal functions unhandled case" e)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (cdddddr ls)
  (cdr (cddddr ls)))

(define (limit-params params)
  (cond
    [(> (length params) 6)
     (append (take params 5)
             (list (append '(tup :) (list (append '(Vector) (map third (cdddddr params)))))))]
    [else params]))

(define (limit-args args)
  (printf "printing args")
  (cond
    [(> (length args) 6) (append (take args 5) (list (Prim 'vector (cdddddr args))))]
    [else args]))

(define (get-convert-dict params)
  (define ans_dict (make-hash))
  (define i 0)
  (for ([param params])
    (cond
      [(>= i 5)
       (dict-set! ans_dict (first param) (Prim 'vector-ref (list (Var 'tup) (Int (- i 5)))))])
    (set! i (+ i 1)))
  ans_dict)

(define (convert-exp env)
  (lambda (e)
    (match e
      [(Var x) (dict-ref! env x (Var x))]
      [(Bool b) (Bool b)]
      [(Void) (Void)]
      [(Int n) (Int n)]
      [(If e1 e2 e3) (If ((convert-exp env) e1) ((convert-exp env) e2) ((convert-exp env) e3))]
      [(Let x e body) (Let x ((convert-exp env) e) ((convert-exp env) body))]
      [(Begin es body) (Begin (map (convert-exp env) es) ((convert-exp env) body))]
      [(SetBang var_sym rhs) (SetBang var_sym ((convert-exp env) rhs))]
      [(WhileLoop cnd body) (WhileLoop ((convert-exp env) cnd) ((convert-exp env) body))]
      [(HasType exp type) (HasType ((convert-exp env) exp) type)]
      [(Prim op es) (Prim op (map (convert-exp env) es))]
      [(Apply fun exps) (Apply ((convert-exp env) fun) (map (convert-exp env) exps))]
      [(FunRef x n) (FunRef x n)]
      [else (error "Convert-exp unhandled case" e)])))

(define (limit_functions e)
  (match e
    [(ProgramDefs info defs) (ProgramDefs info (map limit_functions defs))]
    [(Var x) (Var x)]
    [(FunRef x n) (FunRef x n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(If e1 e2 e3) (If (limit_functions e1) (limit_functions e2) (limit_functions e3))]
    [(Let x e body) (Let x (limit_functions e) (limit_functions body))]
    [(Begin es body) (Begin (map limit_functions es) (limit_functions body))]
    [(SetBang var_sym rhs) (SetBang var_sym (limit_functions rhs))]
    [(WhileLoop cnd body) (WhileLoop (limit_functions cnd) (limit_functions body))]
    [(HasType exp type) (HasType (limit_functions exp) type)]
    [(Prim op es) (Prim op (map limit_functions es))]
    [(Apply fun exps) (Apply (limit_functions fun) (limit-args exps))]
    [(Def name params rty info body)
     (define new_params (limit-params params))
     (define convert-dict (get-convert-dict params))
     (define new_body ((convert-exp convert-dict) body))
     (Def name new_params rty info (limit_functions new_body))]
    [else (error "Limit functions unhandled case" e)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (expose-allocation p)
  (match p
    [(HasType exp type)
     (begin
       (define exps (Prim-arg* exp))
       (define new_exps (map expose-allocation exps))
       (define n (length exps))
       (define array_size (* 8 (+ 1 n)))
       (define arg1 (Prim '+ (list (GlobalValue 'free_ptr) (Int array_size))))
       (define arg2 (GlobalValue 'fromspace_end))
       (define if_cond (If (Prim '< (list arg1 arg2)) (Void) (Collect (Int array_size))))
       (define vec-sym (gensym 'v))
       (define allocate (Allocate n type))
       (define cnt 0)
       (define initialize_eles
         (begin
           (for/list ([an_exp new_exps])
             (define ele (Prim 'vector-set! (list (Var vec-sym) (Int cnt) an_exp)))
             (set! cnt (+ 1 cnt))
             ele)))
       (define vector-declaration (Let vec-sym allocate (Begin initialize_eles (Var vec-sym))))
       (Begin (list if_cond) vector-declaration))]
    [(Var x) (Var x)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Int n) (Int n)]
    [(If e1 e2 e3) (If (expose-allocation e1) (expose-allocation e2) (expose-allocation e3))]
    [(Let x e body) (Let x (expose-allocation e) (expose-allocation body))]
    [(Begin es body) (Begin (map expose-allocation es) (expose-allocation body))]
    [(SetBang var_sym rhs) (SetBang var_sym (expose-allocation rhs))]
    [(Prim op es) (Prim op (map expose-allocation es))]
    [(WhileLoop cnd body) (WhileLoop (expose-allocation cnd) (expose-allocation body))]
    ;; Functions
    [(FunRef x n) (FunRef x n)]
    [(Apply fun exps) (Apply (expose-allocation fun) (map expose-allocation exps))]
    [(Def name params rty info body) (Def name params rty info (expose-allocation body))]
    [(ProgramDefs info defs) (ProgramDefs info (map expose-allocation defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (collect-set! e)
  (match e
    [(Var var) (set)]
    [(Int n) (set)]
    [(Bool b) (set)]
    [(Void) (set)]
    [(Collect n) (set)]
    [(Allocate n type) (set)]
    [(GlobalValue n) (set)]
    [(If e1 e2 e3) (set-union (collect-set! e1) (collect-set! e2) (collect-set! e3))]
    [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(WhileLoop cnd body) (set-union (collect-set! cnd) (collect-set! body))]
    [(Prim op es) (apply set-union (append (map collect-set! es) (list (set))))]
    [(Begin es body) (set-union (apply set-union (append (map collect-set! es) (list (set))))
                                (collect-set! body))]
    ;; Functions
    [(FunRef x n) (set)]
    [(Apply fun exps) (set-union (collect-set! fun)
                                 (apply set-union (append (map collect-set! exps) (list (set)))))]
    [(Def name params rty info body) (collect-set! body)]))

(define (uncover-get!-exp set!-vars)
  (lambda (e)
    (match e
      [(Var x) (if (set-member? set!-vars x) (GetBang x) (Var x))]
      [(Bool x) (Bool x)]
      [(Int x) (Int x)]
      [(Void) (Void)]
      [(Collect n) (Collect n)]
      [(Allocate n type) (Allocate n type)]
      [(GlobalValue n) (GlobalValue n)]
      [(If e1 e2 e3) (If ((uncover-get!-exp set!-vars) e1)
                         ((uncover-get!-exp set!-vars) e2)
                         ((uncover-get!-exp set!-vars) e3))]
      [(Let x rhs body)
       (Let x ((uncover-get!-exp set!-vars) rhs) ((uncover-get!-exp set!-vars) body))]
      [(SetBang var rhs) (SetBang var ((uncover-get!-exp set!-vars) rhs))]
      [(WhileLoop cnd body) (WhileLoop ((uncover-get!-exp set!-vars) cnd)
                                       ((uncover-get!-exp set!-vars) body))]
      [(Prim op es) (Prim op (map (uncover-get!-exp set!-vars) es))]
      [(Begin es body) (Begin (map (uncover-get!-exp set!-vars) es)
                              ((uncover-get!-exp set!-vars) body))]
      ;; Functions
      [(FunRef x n) (FunRef x n)]
      [(Apply fun exps) (Apply ((uncover-get!-exp set!-vars) fun)
                               (map (uncover-get!-exp set!-vars) exps))]
      [(Def name params rty info body)
       (Def name params rty info ((uncover-get!-exp set!-vars) body))])))

(define (uncover-get! p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info
                                          (for/list ([def defs])
                                            (define set!-vars (collect-set! def))
                                            ((uncover-get!-exp set!-vars) def)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return cons(atom, (list (cons variables exp)))
(define (rco-atom expr)
  (define new_sym (gensym 'temp))
  (define new_var (Var new_sym))
  (match expr
    [(Var x) (cons (Var x) '())]
    [(Int x) (cons (Int x) '())]
    [(Bool x) (cons (Bool x) '())]
    [(Void) (cons (Void) '())]
    [(GetBang x) (cons new_var (list (cons new_sym (Var x))))]
    [(Collect n) (cons new_var (list (cons new_sym (Collect n))))]
    [(Allocate n type) (cons new_var (list (cons new_sym (Allocate n type))))]
    [(GlobalValue n) (cons new_var (list (cons new_sym (GlobalValue n))))]
    [(WhileLoop cnd body)
     (cons new_var (list (cons new_sym (WhileLoop (rco-exp cnd) (rco-exp body)))))]
    [(Begin es body) (cons new_var (list (cons new_sym (Begin (map rco-exp es) (rco-exp body)))))]
    [(SetBang x rhs) (cons new_var (list (cons new_sym (SetBang x (rco-exp rhs)))))]
    [(If cmp e1 e2) (let* ([new_sym (gensym 'temp)] ;; refactor this
                           [new_var (Var new_sym)]
                           [list_1 (cons new_sym (If (rco-exp cmp) (rco-exp e1) (rco-exp e2)))])
                      (cons new_var (list list_1)))]
    [(Let x e body) (let* ([new_sym (gensym 'temp)]
                           [new_var (Var new_sym)]
                           [list_1 (cons x (rco-exp e))]
                           [list_2 (cons new_sym (rco-exp body))]
                           [list_3 (append (list list_1) (list list_2))])
                      (cons new_var list_3))]
    [(Apply fun es)
     (let* ([new_sym (gensym 'temp)]
            [new_var (Var new_sym)]
            [pairs (map rco-atom es)]
            [atoms (map car pairs)]
            [fun-ref-pair (rco-atom fun)]
            [fun-ref-atom (car fun-ref-pair)]
            [vs (append (foldr append '() (append (map cdr pairs) (list (cdr fun-ref-pair))))
                        (list (cons new_sym (Apply fun-ref-atom atoms))))])
       (cons new_var vs))]
    [(Prim op es) (let* ([new_sym (gensym 'temp)]
                         [new_var (Var new_sym)]
                         [pairs (map rco-atom es)]
                         [atoms (map car pairs)]
                         [vs (append (foldr append '() (map cdr pairs))
                                     (list (cons new_sym (Prim op atoms))))])
                    (cons new_var vs))]
    [(FunRef x n) (cons new_var (list (cons new_sym (FunRef x n))))]))

(define (gen-lets lst)
  (cond
    [(= 1 (length lst)) (cdar lst)]
    [else (Let (caar lst) (cdar lst) (gen-lets (rest lst)))]))

(define (gen-lets-extra lst)
  (cond
    [(= 1 (length lst)) (Let (caar lst) (cdar lst) (Var (caar lst)))]
    [else (Let (caar lst) (cdar lst) (gen-lets-extra (rest lst)))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int x) (Int x)]
    [(Bool b) (Bool b)]
    [(Collect n) (Collect n)]
    [(Allocate n type) (Allocate n type)]
    [(GlobalValue n) (GlobalValue n)]
    [(Void) (Void)]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (gen-lets (cdr (rco-atom (Prim op es))))]
    [(SetBang x rhs) (SetBang x (rco-exp rhs))]
    [(GetBang x) (Var x)]
    [(WhileLoop cnd body) (WhileLoop (rco-exp cnd) (rco-exp body))]
    [(Begin es body) (Begin (map rco-exp es) (rco-exp body))]
    [(If cmp e1 e2) (If (rco-exp cmp) (rco-exp e1) (rco-exp e2))]
    ;; Functions
    [(FunRef x n) (FunRef x n)]
    [(Apply fun exps) (gen-lets-extra (cdr (rco-atom (Apply fun exps))))]
    [(Def name params rty info body) (Def name params rty info (rco-exp body))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map rco-exp defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define blocks (make-hash))

(define (assign-label blck)
  (match blck
    [(Goto label) (Goto label)]
    [else (let* ([label (gensym 'label)] [_ (dict-set! blocks label blck)] [lab (Goto label)]) lab)]))

(define (assign-block-to-label blck label_sym)
  (begin
    (dict-set! blocks label_sym blck)
    (Goto label_sym)))

;; explicate-pred: Lwhile, e1, e2 -> C1 tail
(define (explicate-pred pred e1 e2)
  (match pred
    [(Bool #t) e1] ;; partial evaluation
    [(Bool #f) e2]
    [(Var x) (let* ([l1 (assign-label e1)] [l2 (assign-label e2)])
               (IfStmt (Prim 'eq? (list (Var x) (Bool #t)))
                       l1
                       l2))] ;; Variable inside if statement, convert to comparison
    [(Prim 'not (list x)) (let* ([l1 (assign-label e1)] [l2 (assign-label e2)])
                            (IfStmt (Prim 'eq? (list x (Bool #f)))
                                    l1
                                    l2))] ;; Variable inside if statement, convert to comparison
    [(Prim cmp (list atm1 atm2)) (let * ([l1 (assign-label e1)] [l2 (assign-label e2)])
                                   (IfStmt (Prim cmp (list atm1 atm2)) l1 l2))]
    [(If cnd exp1 exp2) (let* ([l1 (assign-label e1)]
                               [l2 (assign-label e2)]
                               [B1 (explicate-pred exp1 l1 l2)]
                               [B2 (explicate-pred exp2 l1 l2)])
                          (explicate-pred cnd B1 B2))]
    [(Let x rhs body) (let* ([body (explicate-pred body e1 e2)]) (explicate-assign rhs x body))]
    [(Begin es body) (let* ([tail (explicate-pred body e1 e2)]) (foldr explicate-effect body es))]
    ;; Functions
    ;; TODO apply never in pred since its stored in temp variable
    [else (error "explicate-pred unhandled case" pred)]))

(define (explicate-effect e cont)
  (match e
    [(Var x) cont]
    [(Bool x) cont]
    [(Int x) cont]
    [(Void) cont]
    [(Prim 'read (list)) (Seq (Prim 'read (list)) cont)]
    [(Collect n) (Seq (Collect n) cont)]
    [(Allocate n type) cont]
    [(GlobalValue n) cont]
    [(Prim 'vector-set! es) (Seq (Prim 'vector-set! es) cont)]
    [(Prim op es) cont]
    [(SetBang x rhs) (explicate-assign rhs x cont)]
    [(Let x rhs body) (let* ([body (explicate-effect body cont)]) (explicate-assign rhs x body))]
    [(If cnd e1 e2) (let* ([l1 (assign-label cont)]
                           [tail1 (explicate-effect e1 l1)]
                           [tail2 (explicate-effect e2 l1)])
                      (explicate-pred cnd tail1 tail2))]
    [(Begin es body) (foldr explicate-effect cont (append es (list body)))]
    [(WhileLoop cnd body) (let* ([loop_sym (gensym 'loop)]
                                 [goto_loop (Goto loop_sym)]
                                 [body (explicate-effect body goto_loop)]
                                 [loop (explicate-pred cnd body cont)]
                                 [_ (assign-block-to-label loop loop_sym)])
                            goto_loop)]
    ;; Functions
    [(FunRef label n) cont]
    [(Apply fun exps) (Seq (Call fun exps) cont)]))

;; explicate-tail : Lwhile -> C1 tail
(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Collect n) (Return (Collect n))]
    [(Allocate n type) (Return (Allocate n type))]
    [(GlobalValue n) (Return (GlobalValue n))]
    [(Prim op es) (Return (Prim op es))]
    [(Begin es body) (let* ([tail (explicate-tail body)] [seq (foldr explicate-effect tail es)]) seq)]
    [(Let x rhs body) (let* ([tail (explicate-tail body)] [nt (explicate-assign rhs x tail)]) nt)]
    [(If cnd e1 e2) (let* ([tail1 (explicate-tail e1)] [tail2 (explicate-tail e2)])
                      (explicate-pred cnd tail1 tail2))]
    [(SetBang x rhs) (explicate-assign rhs x (Return Void))]
    [(WhileLoop cnd body) (let* ([loop_sym (gensym 'loop)]
                                 [goto_loop (Goto loop_sym)]
                                 [body (explicate-effect body goto_loop)]
                                 [loop (explicate-pred cnd body (Return (Void)))]
                                 [_ (assign-block-to-label loop loop_sym)])
                            goto_loop)]
    ;; Functions
    [(FunRef label n) (Return (FunRef label n))]
    [(Apply fun exps) (TailCall fun exps)]
    [else (error "explicate-tail unhandled case" e)]))

;; explicate_assign : Lwhile, Var x, C1 tail -> C1 tail
(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Collect n) (Seq (Assign (Var x) (Collect n)) cont)]
    [(Allocate n type) (Seq (Assign (Var x) (Allocate n type)) cont)]
    [(GlobalValue n) (Seq (Assign (Var x) (GlobalValue n)) cont)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd e1 e2) (let* ([l1 (assign-label cont)]
                           [tail1 (explicate-assign e1 x l1)]
                           [tail2 (explicate-assign e2 x l1)])
                      (explicate-pred cnd tail1 tail2))]
    [(Let y rhs body)
     (let* ([tail (explicate-assign body x cont)] [nt (explicate-assign rhs y tail)]) nt)]
    [(Begin es body)
     (let* ([tail (explicate-assign body x cont)] [seq (foldr explicate-effect tail es)]) seq)]
    [(WhileLoop cnd body) (let* ([loop_sym (gensym 'loop)]
                                 [goto_loop (Goto loop_sym)]
                                 [body (explicate-effect body goto_loop)]
                                 [loop (explicate-pred cnd body cont)]
                                 [_ (assign-block-to-label loop loop_sym)])
                            (Seq (Assign (Var x) (Void)) goto_loop))]
    [(SetBang y rhs) (Seq (Assign (Var x) (Void)) (explicate-assign rhs y cont))]
    ;; Functions
    [(FunRef label n) (Seq (Assign (Var x) (FunRef label n)) cont)]
    [(Apply fun exps) (Seq (Assign (Var x) (Call fun exps)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

;; explicate-control : Lwhile -> C1
(define (explicate-control p)
  (match p
    [(ProgramDefs info defs)
     (ProgramDefs
      info
      (for/list ([def defs])
        (set! blocks (make-hash))
        (match def
          [(Def name params type info exp)
           (dict-set! blocks
                      (string->symbol (string-append (symbol->string name) (symbol->string 'start)))
                      (explicate-tail exp))
           (Def name params type info (dict-copy blocks))])))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-mask type position)
  (match type
    [(list) 0]
    [(cons sym remaining) (let* ([isvec (cond
                                          [(equal? sym 'Vector) (expt 2 position)]
                                          [else 0])]
                                 [remainingval (get-mask remaining (+ position 1))])
                            (+ isvec remainingval))]))

(define (get-tag n type)
  (begin
    (define frwd 1)
    (define size (* 2 n)) ;; shift it by one byte
    (define shiftvalue 8) ;; shift to the 8th bit (2 ** 7)
    (define mask (get-mask type shiftvalue))
    (+ mask size frwd)))

;; select-instructions-atom: C0 atom -> pseudo-x86 atom
(define (select-instructions-atm atm)
  (match atm
    [(Var x) (Var x)]
    [(Int x) (Imm x)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(GlobalValue x) (Global x)]
    [(Void) (Imm 0)]
    [else (error "Unhandled atom in select instructions" atm)]))

(define (select-instructions-cmp op)
  (match op
    ['eq? 'e]
    ['> 'g]
    ['< 'l]
    ['>= 'ge]
    ['<= 'le]))

(define (select-instructions-add x a1 a2)
  (cond
    [(eq? x a1)
     (let* ([instr1 (Instr 'addq (list (select-instructions-atm a2) (select-instructions-atm a1)))])
       (list instr1))]
    [(eq? x a2)
     (let* ([instr1 (Instr 'addq (list (select-instructions-atm a1) (select-instructions-atm a2)))])
       (list instr1))]
    [else (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
                 [instr2 (Instr 'addq (list (select-instructions-atm a2) x))])
            (list instr1 instr2))]))

(define (select-instructions-neg x a1)
  (cond
    [(eq? x a1) (let* ([instr1 (Instr 'negq (list (select-instructions-atm a1)))]) (list instr1))]
    [else (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
                 [instr2 (Instr 'negq (list x))])
            (list instr1 instr2))]))

(define (select-instructions-sub x a1 a2)
  (cond
    [(eq? x a1)
     (let* ([instr1 (Instr 'subq (list (select-instructions-atm a2) (select-instructions-atm a1)))])
       (list instr1))]
    [else (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
                 [instr2 (Instr 'subq (list (select-instructions-atm a2) x))])
            (list instr1 instr2))]))

(define (select-instructions-exp p)
  (match p
    [(Seq x y) (append (select-instructions-exp x) (select-instructions-exp y))]
    [(Assign x (Prim '+ (list a1 a2))) (select-instructions-add x a1 a2)]
    [(Assign x (Prim '- (list a1))) (select-instructions-neg x a1)]
    [(Assign x (Prim '- (list a1 a2))) (select-instructions-sub x a1 a2)]
    [(Prim 'read '()) (list (Callq 'read_int 0))]
    [(Assign x (Allocate n type))
     (let* ([instr1 (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))]
            [instr2 (Instr 'addq (list (Imm (* 8 (+ n 1))) (Global 'free_ptr)))]
            [instr3 (Instr 'movq (list (Imm (get-tag n type)) (Deref 'r11 0)))]
            [instr4 (Instr 'movq (list (Reg 'r11) x))])
       (list instr1 instr2 instr3 instr4))]
    [(Prim 'vector-set! (list vec (Int pos) an_exp)) ;; vector ref can be a statement
     (let* ([instr1 (Instr 'movq (list vec (Reg 'r11)))]
            [instr2
             (Instr 'movq (list (select-instructions-atm an_exp) (Deref 'r11 (* (+ 1 pos) 8))))])
       (list instr1 instr2))]
    [(Assign x (Prim 'vector-set! (list vec (Int pos) an_exp)))
     (let* ([instr1 (Instr 'movq (list vec (Reg 'r11)))]
            [instr2
             (Instr 'movq (list (select-instructions-atm an_exp) (Deref 'r11 (* (+ 1 pos) 8))))]
            [instr3 (Instr 'movq (list (Var x) (Imm 0)))])
       (list instr1 instr2 instr3))]
    [(Assign x (Prim 'vector-ref (list vec (Int pos))))
     (let* ([instr1 (Instr 'movq (list vec (Reg 'r11)))]
            [instr2 (Instr 'movq (list (Deref 'r11 (* (+ 1 pos) 8)) x))])
       (list instr1 instr2))]
    [(Assign x (Prim 'vector-length (list vec))) (let* ([instr1 (Instr 'movq (list vec (Reg 'r11)))]
                                                        [instr2 (Instr 'movq (list (Deref 'r11 0) x))]
                                                        [instr3 (Instr 'sarq (list (Imm 1) x))]
                                                        [instr4 (Instr 'andq (list (Imm 127) x))])
                                                   (list instr1 instr2 instr3 instr4))]
    [(Collect (Int n)) (let* ([instr1 (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))]
                              [instr2 (Instr 'movq (list (Imm n) (Reg 'rsi)))]
                              [instr3 (Callq 'collect 2)])
                         (list instr1 instr2 instr3))]
    [(Assign x (Prim 'read '())) (let* ([instr1 (Callq 'read_int 0)]
                                        [instr2 (Instr 'movq (list (Reg 'rax) x))])
                                   (list instr1 instr2))]
    [(Assign x (Prim 'not (list a1)))
     (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
            [instr2 (Instr 'xorq (list (Imm 1) x))])
       (list instr1 instr2))]
    [(Assign x (Prim cmp (list a1 a2)))
     (let* ([instr1 (Instr 'cmpq
                           (list (select-instructions-atm a2)
                                 (select-instructions-atm a1)))] ;; Args flipped in cmpq
            [instr2 (Instr 'set (list (select-instructions-cmp cmp) (Reg 'al)))]
            [instr3 (Instr 'movzbq (list (Reg 'al) x))])
       (list instr1 instr2 instr3))]
    ;; Functions
    [(Assign x (FunRef label n)) (list (Instr 'leaq (list (Global label) x)))]
    [(Assign x (Call fun args))
     (define regs (map Reg '(rdi rsi rdx rcx r8 r9)))
     (define instrs_mov_args
       (for/list ([arg args] [reg regs])
         (Instr 'movq (list (select-instructions-atm arg) reg))))
     (define call_instr (IndirectCallq fun (length args)))
     (define res_move (Instr 'movq (list (Reg 'rax) x)))
     (flatten (list instrs_mov_args call_instr res_move))]
    ;; Reassign variable
    [(Assign x y) (let* ([instr1 (Instr 'movq (list (select-instructions-atm y) x))]) (list instr1))]
    ;; Tails
    [(TailCall fun args)
     (define regs (map Reg '(rdi rsi rdx rcx r8 r9)))
     (define instrs_mov_args
       (for/list ([arg args] [reg regs])
         (Instr 'movq (list (select-instructions-atm arg) reg))))
     (define call_instr (TailJmp fun (length args)))
     (flatten (list instrs_mov_args call_instr))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim cmp (list a1 a2)) (Goto l1) (Goto l2))
     (let* ([instr1 (Instr 'cmpq
                           (list (select-instructions-atm a2)
                                 (select-instructions-atm a1)))] ;; Args flipped in cmpq
            [instr2 (JmpIf (select-instructions-cmp cmp) l1)]
            [instr3 (Jmp l2)])
       (list instr1 instr2 instr3))]
    [(Return e) (let * ([instrs (select-instructions-exp (Assign (Reg 'rax) e))]
                        [instr2 (Jmp (conclusion-name fn-name))])
                  (append instrs (list instr2)))]))

(define (select-instructions-block blck)
  (match blck
    [(cons label cmds) (cons label (Block '() (select-instructions-exp cmds)))]))

(define (start-name name)
  (string->symbol (string-append (symbol->string name) (symbol->string 'start))))

(define (conclusion-name name)
  (string->symbol (string-append (symbol->string name) (symbol->string 'conclusion))))
(define fn-name 'abcd)
(define (select-instructions-def def)
  (match def
    [(Def name params type info body)
     (set! fn-name name)
     (define regs (map Reg '(rdi rsi rdx rcx r8 r9)))
     (define new_instrs empty)
     (for ([param params] [reg regs])
       (set! new_instrs (append new_instrs (list (Instr 'movq (list reg (Var (car param))))))))
     (define new_body (map select-instructions-block (hash->list body)))
     (define instrs_for_start (Block-instr* (dict-ref new_body (start-name name))))
     (define newer_body
       (dict-set new_body (start-name name) (Block '() (append new_instrs instrs_for_start))))
     (define new_info (dict-set info 'num-params (length params)))
     (Def name '() type new_info newer_body)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map select-instructions-def defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (var-offset-mapping var_list position)
  (cond
    [(empty? var_list) (list)]
    [else (cons (list (car var_list) position) (var-offset-mapping (cdr var_list) (- position 8)))]))

(define (assign-home-instr-list inst_list var_stack_mapping)
  (for/list ([inst inst_list])
    (match inst
      [(Instr op args) (Instr op
                              (for/list ([arg args])
                                (match arg
                                  [(Var v) (Deref 'rbp (first (dict-ref var_stack_mapping v)))]
                                  [else arg])))]
      [else inst])))

(define (assign-homes-blocks cur_block var_stack_mapping)
  (match cur_block
    [(cons label (Block info instr_list))
     (cons label (Block info (assign-home-instr-list instr_list var_stack_mapping)))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (X86Program
      info
      (let* ([var_stack_mapping (var-offset-mapping (dict-keys (dict-ref info 'locals-types)) -8)]
             [new_blocks (map (lambda (x) (assign-homes-blocks x var_stack_mapping)) blocks)])
        new_blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : psuedo-x86 -> x86

(define (fix-instructions inst_list)
  (for/list ([inst inst_list])
    (match inst
      [(Instr 'movq (list arg arg)) empty] ;; remove all moves with some source and destination
      [(Instr 'movzbq (list arg1 (Deref reg1 off1))) ;; second argument of movzbq must be a register
       (list (Instr 'movzbq (list arg1 (Reg 'rax))) ;; TODO backtest everything
             (Instr 'movq (list (Reg 'rax) (Deref reg1 off1))))]
      ;; second argument of leaq must be a register TODO make a test for it
      [(Instr 'leaq (list arg1 (Deref reg1 off1)))
       (list (Instr 'leaq (list arg1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref reg1 off1))))]
      [(Instr 'cmpq (list arg1 (Imm x))) ;; second argument of cmpq must not be an immediate
       (let* ([instr1 (Instr 'movq (list (Imm x) (Reg 'rax)))]
              [instr2 (Instr 'cmpq (list arg1 (Reg 'rax)))])
         (list instr1 instr2))]
      [(Instr op
              (list (Deref reg1 off1)
                    (Deref reg2 off2))) ;; No two memory reference in one instruction
       (let* ([instr1 (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))]
              [instr2 (Instr op (list (Reg 'rax) (Deref reg2 off2)))])
         (list instr1 instr2))]
      [(TailJmp target n) (list (Instr 'movq (list target (Reg 'rax))) (TailJmp (Reg 'rax) n))]
      [else inst])))

(define (patch-block pr)
  (cons (car pr)
        (match (cdr pr)
          [(Block info instrs) (Block info (flatten (fix-instructions instrs)))]
          [else
           error
           "Not a valid block"])))

(define (patch-instructions-def def)
  (match def
    [(Def name params type info blocks) (Def name params type info (map patch-block blocks))]))

(define (patch-instructions p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map patch-instructions-def defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; prelude-and-conclusion : x86 -> x86

(define (pnc-def def)
  (match def
    [(Def name params type info blocks)
     (set! fn-name name)
     (let* ([stacksize (* 8 (length (dict-keys (dict-ref info 'locals-types))))]
            [stacksize (+ stacksize (modulo stacksize 16))]
            [callee-saved (dict-ref info 'used_callee)]
            [instr1 (Instr 'pushq (list (Reg 'rbp)))]
            [instr2 (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))]
            [instr-callee-push (for/list ([reg callee-saved])
                                 (Instr 'pushq (list reg)))]
            [instr-callee-pop (for/list ([reg callee-saved])
                                (Instr 'popq (list reg)))]
            [callee-size (* 8 (length callee-saved))]
            [spills (dict-ref info 'num_spilled)]
            [local_var_size (* 8 spills)]
            [stacksize (+ callee-size local_var_size)]
            [stacksize (+ stacksize (modulo stacksize 16))]
            [stacksize (- stacksize callee-size)]
            [root-stack-instrs (list (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
                                     (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
                                     (Callq 'initialize 2)
                                     (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15))))]
            [root-stack-instrs2 (make-list (dict-ref info 'num-root-spills)
                                           (list (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
                                                 (Instr 'addq (list (Imm 8) (Reg 'r15)))))]
            [instr3 (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))]
            [instr4 (Jmp (start-name fn-name))]
            [instr_mov_r15 (Instr 'subq (list (Imm (* 8 (dict-ref info 'num-root-spills))) (Reg 'r15)))]
            [instr5 (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))]
            [instr6 (Instr 'popq (list (Reg 'rbp)))]
            [instr7 (Retq)]

            [main_block
             (if (eq? fn-name 'main)
                 (Block empty
                        (flatten (list instr1
                                       instr2
                                       instr-callee-push
                                       instr3
                                       root-stack-instrs
                                       root-stack-instrs2
                                       instr4)))

                 (Block empty (flatten (list instr1 instr2 instr-callee-push root-stack-instrs2 instr3 instr4))))]
            [conclusion_block (Block empty (flatten (list instr5 instr-callee-pop instr_mov_r15 instr6 instr7)))]
            [blocks (dict-set* blocks fn-name main_block (conclusion-name fn-name) conclusion_block)])
       blocks)]))

(define (prelude-and-conclusion p)
  (match p
    [(ProgramDefs info defs) (X86Program info (flatten-one (map pnc-def defs)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define global-blocks (make-hash))

(define (filter-var-reg lst)
  (list->set (filter (lambda (x) (or (Var? x) (Reg? x))) lst)))

(define (instr-location-read instr)
  (let* ([live_list (match instr
                      [(Instr 'movq (list arg1 arg2)) (list arg1)]
                      [(Instr 'movzbq (list arg1 arg2)) (list arg1)]
                      [(Instr 'leaq (list arg1 arg2)) (list arg1)]
                      [(Instr 'set (list cc arg)) empty] ;; Read from eflags
                      [(Instr op args) args] ;; Read from eflags
                      [(Callq x y) (map Reg (take '(rdi rsi rdx rcx r8 r9) y))]
                      ;; Functions
                      [(IndirectCallq x y) (map Reg (take '(rdi rsi rdx rcx r8 r9) y))]
                      [(TailJmp x y) (map Reg (take '(rdi rsi rdx rcx r8 r9) y))]
                      [(Jmp label) empty]
                      [(JmpIf cc label) empty]
                      [else (error "Invalid instruction" instr)])]
         [filter_list (filter (lambda (x) (or (Var? x) (Reg? x))) live_list)])
    (list->set filter_list)))

(define (instr-location-written instr)
  (let* ([live_list (match instr
                      [(Instr 'cmpq es) empty]
                      [(Instr 'set (list cc arg)) (list (Reg 'rax))] ;; Only using rax for now
                      [(Instr op es) (list (last es))]
                      [(Callq x y) (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11))]
                      [(IndirectCallq x y) (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11))]
                      [(TailJmp x y) (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11))]
                      [(Jmp label) empty]
                      [(JmpIf cc label) empty]
                      [else (error "Invalid instruction" instr)])]
         [filter_list (filter (lambda (x) (or (Var? x) (Reg? x))) live_list)])
    (list->set filter_list)))

(define (uncover-live-instrs instrs prev_liveness)
  (define reverse-instrs (reverse instrs))
  (define liveness
    (for/list ([instr reverse-instrs])
      (define locations_read (instr-location-read instr))
      (define locations_written (instr-location-written instr))
      (define new_liveness (set-union (set-subtract prev_liveness locations_written) locations_read))
      (set! prev_liveness new_liveness)
      new_liveness))
  (reverse liveness))

(define (analyze_dataflow G transfer bottom join)
  ;; make an empty map
  (define mapping (make-hash))

  ;; empty hash of each label is empty set
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))

  ;; fill the queue with labels
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))

  (define trans-G (transpose G))

  (while (not (queue-empty? worklist))
         ;; get top label from queue
         (define node (dequeue! worklist))
         (printf "~a\n" node)
         ;; do set union over all the mappings of neighbours of node
         (define input
           (for/fold ([state bottom]) ([pred (in-neighbors trans-G node)])
             (join state (dict-ref mapping pred))))
         (printf "~a\n" node)
         ;; get output of the node using transfer function
         (define output (transfer node input))
         (cond
           [(not (equal? output (dict-ref mapping node)))
            (dict-set! mapping node output)
            (for ([v (in-neighbors G node)])
              (enqueue! worklist v))]))
  mapping)

(define (transfer! blck_label live_after_set)
  (cond
    [(eq? blck_label (conclusion-name fn-name)) (set (Reg 'rax) (Reg 'rsp))]
    [else
     (define blck (dict-ref global-blocks blck_label))
     (define instrs (Block-instr* blck))
     (define info (Block-info blck))
     (define liveness (uncover-live-instrs instrs live_after_set))
     (define info_new (dict-set info 'liveness liveness))
     (define new_block (Block info_new instrs))
     (dict-set! global-blocks blck_label new_block)
     (first liveness)]))

(define (uncover-live-def def)
  (set! global-blocks (make-hash))
  (match def
    [(Def name params type info blocks)
     (set! fn-name name)
     (let* ([CFG (multigraph (make-hash))]
            [_ (for ([blck blocks])
                 (dict-set! global-blocks (car blck) (cdr blck))
                 (let* ([label (car blck)]
                        [instrs (Block-instr* (cdr blck))]
                        [_ (for ([instr instrs])
                             (match instr
                               [(Jmp label_to) (add-directed-edge! CFG label label_to)]
                               [(JmpIf cc label_to) (add-directed-edge! CFG label label_to)]
                               [else 0]))])
                   0))]
            [transposed-CFG (transpose CFG)]
            [_ (analyze_dataflow transposed-CFG transfer! (set) set-union)])
       (Def name params type info (hash->list global-blocks)))]))

(define (uncover_live p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map uncover-live-def defs))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-interference-edges instr_k l_after)
  (let* ([var_written (match instr_k
                        [(Instr 'movq es) (filter-var-reg es)]
                        [(Instr 'movzbq es) (filter-var-reg es)]
                        [else (instr-location-written instr_k)])]
         [l_left (set-subtract l_after var_written)] ;; remove both d, s from l_after in case of movq
         [l_left_list (set->list l_left)]
         [var_written_list (set->list var_written)]
         [var_written_list
          (match instr_k
            [(Instr 'movq es) (list (last es))] ;; incase of movq only make edges from the dest
            [(Instr 'movzbq es) (list (last es))] ;; incase of movzbq only make edges from the dest
            [else var_written_list])] ;; make edges from all the written variables
         [edges (cartesian-product var_written_list l_left_list)])
    edges))

(define (flatten-one lst)
  (foldr append '() lst))

(define (get-liveness-from-block blck)
  (let* ([info (Block-info (cdr blck))]
         [liveness (dict-ref info 'liveness)]
         [liveness (append (cdr liveness) (list (set)))]) ;; TODO confirm this
    liveness))

(define (remove-liveness blck)
  (match blck
    [(cons label (Block info instrs)) (cons label (Block (dict-remove info 'liveness) instrs))]))

(define (build-move-graph instrs)
  (match instrs
    [(list) empty]
    [(list (Instr 'movq (list (Var x) (Var y))) rst ...)
     (cons (list (Var x) (Var y)) (build-move-graph (rest instrs)))]
    [else (build-move-graph (rest instrs))]))

(define (build-interference-def def)
  (match def
    [(Def name params type info blocks)
     (let* ([instrs (flatten-one (map (lambda (blck) (Block-instr* (cdr blck))) blocks))]
            [liveness (flatten-one (map get-liveness-from-block blocks))]
            [blocks (map remove-liveness blocks)]
            [types (dict-ref info 'locals-types)]
            [edges (map get-interference-edges instrs liveness)]
            [tuple-typed-vars (map car (filter (lambda (x) (list? (cdr x))) types))]
            [callee-saved (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11 rsp rbp rbx r12 r13 r14 r15))]
            [edges2 (cartesian-product tuple-typed-vars callee-saved)]
            [edges (append edges edges2)]
            [graph (undirected-graph (foldr append '() edges))]
            [mg (undirected-graph (build-move-graph instrs))]
            [mg-edges (get-edges mg)]
            [info (dict-set* info
                             'conflicts
                             graph
                             'move-graph
                             mg
                             'mg-edges
                             mg-edges
                             'num-root-spills
                             (length tuple-typed-vars))])
       (Def name params type info blocks))]))

(define (build-interference p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map build-interference-def defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (saturation-cmp x y)
  (match* (x y)
    [((cons var_x sat_x) (cons var_y sat_y)) (> (set-count sat_x) (set-count sat_y))]
    [(_ _) (error "Invalid comparison")]))

(define (get-var x)
  (car (node-key x)))
(define (get-sat x)
  (cdr (node-key x)))

(define (find-handle-neigh handle neighbours)
  (or (member (Reg (get-var handle)) neighbours) (member (Var (get-var handle)) neighbours)))

(define (update-saturation handle color pq)
  (let* ([var (get-var handle)]
         [saturation (get-sat handle)]
         [new_sat (set-union saturation (set color))])
    (set-node-key! handle (cons var new_sat)) ;; update the saturation set in the node
    (pqueue-decrease-key! pq handle))) ;; tell pq to change order

(define (update-saturations graph handles var color pq)
  (define neighbours (sequence->list (in-neighbors graph var)))
  (define var_neighbours (filter Var? neighbours)) ;; update only the saturation of variables
  (for ([neighbour var_neighbours])
    (define handle
      (dict-ref handles (Var-name neighbour) #f)) ;; check if the variable still exists in handles
    (if handle (update-saturation handle color pq) 0)))

(define (get_greedy_color sat_popped num)
  (if (set-member? sat_popped num) (get_greedy_color sat_popped (+ num 1)) num))

(define (not-while-loop n graph handles pq)
  (cond
    [(= n 0) '()]
    [else (let* ([node_popped (pqueue-pop! pq)]
                 [var_popped (car node_popped)]
                 [sat_popped (cdr node_popped)]
                 [reqd_color (get_greedy_color sat_popped 0)]
                 [color_pair (cons (Var var_popped) reqd_color)]
                 [_ (dict-remove! handles var_popped)] ;; remove the popped element from handles
                 [_ (update-saturations graph handles (Var var_popped) reqd_color pq)]
                 [lst (append (list color_pair) (not-while-loop (- n 1) graph handles pq))])
            lst)]))

(define (color_graph graph vars)
  (let* ([vertices (get-vertices graph)]
         [registers-used (filter (lambda (x) (Reg? x)) vertices)]
         [var_color '()]
         [pq (make-pqueue saturation-cmp)]
         [handles (make-hash)]
         [_ (for ([var vars]) ;; note var is a symbol not a variable
              (define handle (pqueue-push! pq (cons var (set))))
              (dict-set! handles var handle))]
         [_ (for ([reg registers-used])
              (define reg_name (Reg-name reg))
              (set! var_color (append var_color (list (cons reg (register->color reg_name)))))
              (update-saturations graph handles reg (register->color reg_name) pq))]
         [n (pqueue-count pq)]
         [vars (not-while-loop n graph handles pq)]
         [var_color (append var_color vars)])
    var_color))

(define (get-color-to-home colors num_used_callee)
  (let* ([max_register (num-registers-for-alloc)]
         [cth (for/list ([color colors])
                (cond
                  [(< color max_register) (cons color (Reg (color->register color)))]
                  [else (let* ([offset 8]
                               [callee_space (* 8 num_used_callee)]
                               [offset_space (* 8 (- color max_register))]
                               [total_offset (+ offset (+ callee_space offset_space))]
                               [total_offset (- total_offset)])
                          (cons color (Deref 'rbp total_offset)))]))])
    cth))
(define root-offsets (make-hash))
(define counter 0)

(define (allocate-register-instrs inst_list vtc cth tuples)
  (for/list ([inst inst_list])
    (match inst
      [(Instr op args)
       (Instr op
              (for/list ([arg args])
                (match arg
                  [(Var v) (if (member v tuples)
                               (let ([offset (dict-ref root-offsets
                                                       v
                                                       (lambda ()
                                                         (begin
                                                           (set! counter (+ 1 counter))
                                                           (dict-set! root-offsets v counter)
                                                           counter)))])
                                 (Deref 'r15 (* offset 8)))
                               (let* ([color (dict-ref vtc (Var v))] [home (dict-ref cth color)])
                                 home))]
                  [else arg])))]

      [(IndirectCallq arg n)
       (IndirectCallq
        (match arg
          [(Var v) (if (member v tuples)
                       (let ([offset (dict-ref root-offsets
                                               v
                                               (lambda ()
                                                 (begin
                                                   (set! counter (+ 1 counter))
                                                   (dict-set! root-offsets v counter)
                                                   counter)))])
                         (Deref 'r15 (* offset 8)))
                       (let* ([color (dict-ref vtc (Var v))] [home (dict-ref cth color)]) home))]
          [else arg])
        n)]
      [(TailJmp arg n)
       (TailJmp
        (match arg
          [(Var v) (if (member v tuples)
                       (let ([offset (dict-ref root-offsets
                                               v
                                               (lambda ()
                                                 (begin
                                                   (set! counter (+ 1 counter))
                                                   (dict-set! root-offsets v counter)
                                                   counter)))])
                         (Deref 'r15 (* offset 8)))
                       (let* ([color (dict-ref vtc (Var v))] [home (dict-ref cth color)]) home))]
          [else arg])
        n)]
      [else inst])))

(define (allocate-register-block cur_block vtc cth tuples)
  (match cur_block
    [(cons label (Block info instr_list))
     (cons label (Block info (allocate-register-instrs instr_list vtc cth tuples)))]))

(define (allocate-registers-def def)
  (match def
    [(Def name param type info blocks)
     (let* ([var-to-color (color_graph (dict-ref info 'conflicts)
                                       (dict-keys (dict-ref info 'locals-types)))]
            [info (dict-set info 'colors var-to-color)]
            [colors (list->set (filter (lambda (x) (>= x 0)) (map cdr var-to-color)))]
            [used_callee
             (map Reg '(rbx r12 r13 r14))] ;; assume we are using all the callee saved registers
            [num_used_callee (set-count used_callee)]
            [color-to-home (get-color-to-home colors num_used_callee)]
            [num_spilled (length (filter (lambda (x) (Deref? (cdr x))) color-to-home))]
            [info (dict-set info 'used_callee used_callee)]
            [info (dict-set info 'num_spilled num_spilled)]
            [info (dict-set info 'homes color-to-home)]
            [info (dict-remove info 'liveness)]
            [tuples (map car (filter (lambda (x) (list? (cdr x))) (dict-ref info 'locals-types)))]
            [_ (set! root-offsets (make-hash))]
            [_ (set! counter 0)]
            [new_blocks
             (map (lambda (x) (allocate-register-block x var-to-color color-to-home tuples)) blocks)])
       (Def name param type info new_blocks))]))

(define (allocate-registers p)
  (match p
    [(ProgramDefs info defs) (ProgramDefs info (map allocate-registers-def defs))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; ("partial evaluation" ,pe-Lvar ,interp-Lvar)
  `(("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
    ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
    ("reveal_functions" ,reveal_functions ,interp-Lfun-prime ,type-check-Lfun)
    ("limit_functions" ,limit_functions ,interp-Lfun-prime ,type-check-Lfun)
    ("expose_allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
    ("uncover-get!" ,uncover-get! ,interp-Lfun-prime ,type-check-Lfun)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lfun-prime ,type-check-Lfun)
    ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-3)
    ("liveness analysis" ,uncover_live ,interp-pseudo-x86-3)
    ("build interference" ,build-interference ,interp-pseudo-x86-3)
    ("allocate registers" ,allocate-registers ,interp-pseudo-x86-3)
    ("patch instructions" ,patch-instructions ,interp-x86-3)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-3)

    ))
