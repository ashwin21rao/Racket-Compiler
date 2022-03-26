#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
(require graph)
;; (require "interp-Lint.rkt")
;; (require "interp-Lvar.rkt")
;; (require "interp-Cvar.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cif.rkt")
(require "interp.rkt")

(require "utilities.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
(require racket/trace)
;; (require "type-check-Lvar.rkt")
;; (require "type-check-Cvar.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cif.rkt")
(require "type-check-Cwhile.rkt")

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

;; shrink Lwhile -> Lwhile
(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink e))]
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
    [else (error "Shrink unhandled case" p)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
      [(Prim op es) (Prim op (map (uniquify-exp env) es))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (collect-set! e)
  (match e
    [(Var var) (set)]
    [(Int n) (set)]
    [(Bool b) (set)]
    [(Void) (set)]
    [(If e1 e2 e3) (set-union (collect-set! e1) (collect-set! e2) (collect-set! e3))]
    [(Let x rhs body) (set-union (collect-set! rhs) (collect-set! body))]
    [(SetBang var rhs) (set-union (set var) (collect-set! rhs))]
    [(WhileLoop cnd body) (set-union (collect-set! cnd) (collect-set! body))]
    [(Prim op es) (apply set-union (append (map collect-set! es) (list (set))))]
    [(Begin es body) (set-union (apply set-union (map collect-set! es)) (collect-set! body))]))

(define (uncover-get!-exp e set!-vars)
  (match e
    [(Var x) (if (set-member? set!-vars x) (GetBang x) (Var x))]
    [(Bool x) (Bool x)]
    [(Int x) (Int x)]
    [(Void) (Void)]
    [(If e1 e2 e3) (If (uncover-get!-exp e1 set!-vars) (uncover-get!-exp e2 set!-vars) (uncover-get!-exp e3 set!-vars))]
    [(Let x rhs body) (Let x (uncover-get!-exp rhs set!-vars) (uncover-get!-exp body set!-vars))]
    [(SetBang var rhs) (SetBang var (uncover-get!-exp rhs set!-vars))]
    [(WhileLoop cnd body) (WhileLoop (uncover-get!-exp cnd set!-vars)
                                     (uncover-get!-exp body set!-vars))]
    [(Prim op es) (Prim op (map (lambda (x) (uncover-get!-exp x set!-vars)) es))]
    [(Begin es body) (Begin (map (lambda (x) (uncover-get!-exp x set!-vars)) es)
                            (uncover-get!-exp body set!-vars))]))

(define (uncover-get! p)
  (match p
    [(Program info e) (let ([set!-vars (collect-set! e)])
                        (Program info (uncover-get!-exp e set!-vars)))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return cons(atom, (list (cons variables exp)))
(define (rco-atom expr)
  (match expr
    [(Var x) (cons (Var x) '())]
    [(Int x) (cons (Int x) '())]
    [(Bool x) (cons (Bool x) '())]
    [(If cmp e1 e2) (let* ([new_sym (gensym 'temp)]
                           [new_var (Var new_sym)]
                           [list_1 (cons new_sym (If (rco-exp cmp) (rco-exp e1) (rco-exp e2)))])
                      (cons new_var (list list_1)))]
    [(Let x e body) (let* ([new_sym (gensym 'temp)]
                           [new_var (Var new_sym)]
                           [list_1 (cons x (rco-exp e))]
                           [list_2 (cons new_sym (rco-exp body))]
                           [list_3 (append (list list_1) (list list_2))])
                      (cons new_var list_3))]
    [(Prim op es) (let* ([new_sym (gensym 'temp)]
                         [new_var (Var new_sym)]
                         [pairs (map rco-atom es)]
                         [atoms (map car pairs)]
                         [vs (append (foldr append '() (map cdr pairs))
                                     (list (cons new_sym (Prim op atoms))))])
                    (cons new_var vs))]))

(define (gen-lets lst)
  (cond
    [(= 1 (length lst)) (cdar lst)]
    [else (Let (caar lst) (cdar lst) (gen-lets (rest lst)))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int x) (Int x)]
    [(Bool b) (Bool b)]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (gen-lets (cdr (rco-atom (Prim op es))))]
    [(If cmp e1 e2) (If (rco-exp cmp) (rco-exp e1) (rco-exp e2))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define blocks (make-hash))

(define (assign-label blck)
  (match blck
    [(Goto label) (Goto label)]
    [else (let* ([label (gensym 'label)] [_ (dict-set! blocks label blck)] [lab (Goto label)]) lab)]))

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
    [else (error "explicate-pred unhandled case" pred)]))

;; explicate-tail : Lwhile -> C1 tail
(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Bool b) (Return (Bool b))]
    [(Prim op es) (Return (Prim op es))]
    [(Let x rhs body) (let* ([tail (explicate-tail body)] [nt (explicate-assign rhs x tail)]) nt)]
    [(If cnd e1 e2) (let* ([tail1 (explicate-tail e1)] [tail2 (explicate-tail e2)])
                      (explicate-pred cnd tail1 tail2))]
    [else (error "explicate-tail unhandled case" e)]))

;; explicate_assign : Lwhile, Var x, C1 tail -> C1 tail
(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b) (Seq (Assign (Var x) (Bool b)) cont)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If cnd e1 e2) (let* ([l1 (assign-label cont)]
                           [tail1 (explicate-assign e1 x l1)]
                           [tail2 (explicate-assign e2 x l1)])
                      (explicate-pred cnd tail1 tail2))]
    [(Let y rhs body)
     (let* ([tail (explicate-assign body x cont)] [nt (explicate-assign rhs y tail)]) nt)]
    [else (error "explicate-assign unhandled case" e)]))

;; explicate-control : Lwhile -> C1
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info
                                   (let* ([_ (set! blocks (make-hash))]
                                          [a (dict-set! blocks 'start (explicate-tail body))])
                                     blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; select-instructions-atom: C0 atom -> pseudo-x86 atom
(define (select-instructions-atm atm)
  (match atm
    [(Var x) (Var x)]
    [(Int x) (Imm x)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
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
    [(Assign x y) (let* ([instr1 (Instr 'movq (list (select-instructions-atm y) x))]) (list instr1))]
    [(Goto label) (list (Jmp label))]
    [(IfStmt (Prim cmp (list a1 a2)) (Goto l1) (Goto l2))
     (let* ([instr1 (Instr 'cmpq
                           (list (select-instructions-atm a2)
                                 (select-instructions-atm a1)))] ;; Args flipped in cmpq
            [instr2 (JmpIf (select-instructions-cmp cmp) l1)]
            [instr3 (Jmp l2)])
       (list instr1 instr2 instr3))]
    [(Return e)
     (let * ([instrs (select-instructions-exp (Assign (Reg 'rax) e))] [instr2 (Jmp 'conclusion)])
       (append instrs (list instr2)))]))

(define (select-instructions-block blck)
  (match blck
    [(cons label cmds) (cons label (Block '() (select-instructions-exp cmds)))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info blocks) (X86Program info (map select-instructions-block (hash->list blocks)))]))

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
       (let* ([instr1 (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))]
              [instr2 (Instr 'movzbq (list arg1 (Reg 'rax)))])
         (list instr1 instr2))]
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
      [else inst])))

(define (patch-block pr)
  (cons (car pr)
        (match (cdr pr)
          [(Block info instrs) (Block info (flatten (fix-instructions instrs)))]
          [else
           error
           "Not a valid block"])))

(define (patch-instructions p)
  (match p
    [(X86Program info blocks) (X86Program info (map patch-block blocks))]))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (X86Program
      info
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
             [instr3 (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))]
             [instr4 (Jmp 'start)]
             [instr5 (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))]
             [instr6 (Instr 'popq (list (Reg 'rbp)))]
             [instr7 (Retq)]
             [main_block (Block empty (flatten (list instr1 instr2 instr-callee-push instr3 instr4)))]
             [conclusion_block (Block empty (flatten (list instr5 instr-callee-pop instr6 instr7)))]
             [blocks (dict-set* blocks 'main main_block 'conclusion conclusion_block)])
        blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define label->live (make-hash))

(define (filter-var-reg lst)
  (list->set (filter (lambda (x) (or (Var? x) (Reg? x))) lst)))

(define (instr-location-read instr)
  (let* ([live_list (match instr
                      [(Instr 'movq (list arg1 arg2)) (list arg1)]
                      [(Instr 'movzbq (list arg1 arg2)) (list arg1)]
                      [(Instr 'set (list cc arg)) empty] ;; Read from eflags
                      [(Instr op args) args] ;; Read from eflags
                      #| [(Instr 'addq atoms) atoms] |#
                      #| [(Instr 'subq atoms) atoms] |#
                      #| [(Instr 'negq (list arg1)) (list arg1)] |#
                      #| [(Instr 'xorq (list arg1 arg2)) (list arg1 arg2)] |#
                      #| [(Instr 'cmpq es) es] |#
                      [(Callq x y) (map Reg
                                        (take '(rdi rsi rdx rcx r8 r9)
                                              y))] ;; TODO what happens if more than 6 args
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
                      [(Jmp label) empty]
                      [(JmpIf cc label) empty]
                      [else (error "Invalid instruction" instr)])]
         [filter_list (filter (lambda (x) (or (Var? x) (Reg? x))) live_list)])
    (list->set filter_list)))

(define (uncover-live-instrs instrs prev_liveness)
  (match instrs
    [(list) empty]
    [else
     (let* ([instr (first instrs)]
            [prev_liveness (match instr
                             [(Jmp label) (dict-ref label->live label)]
                             [(JmpIf cc label)
                              (set-union (dict-ref label->live label)
                                         prev_liveness)] ;; Take union with prev liveness
                             [else prev_liveness])]
            [locations_read (instr-location-read instr)]
            [locations_written (instr-location-written instr)]
            [new_liveness (set-union (set-subtract prev_liveness locations_written) locations_read)])
       (append (uncover-live-instrs (rest instrs) new_liveness) (list new_liveness)))]))

(define (uncover-live-block blocks label)
  (match (cons label (dict-ref blocks label))
    [(cons label (Block info instrs))
     (let* ([info (dict-set info 'liveness (uncover-live-instrs (reverse instrs) (list (set))))]
            [_ (dict-set! label->live label (first (dict-ref info 'liveness)))])
       (cons label (Block info instrs)))]))

(define (uncover_live p)
  (match p
    [(X86Program info blocks)
     (let* ([CFG (multigraph (make-hash))]
            [_ (for ([blck blocks])
                 (let* ([label (car blck)]
                        [instrs (Block-instr* (cdr blck))]
                        [_ (for ([instr instrs])
                             (match instr
                               [(Jmp label_to) (add-directed-edge! CFG label label_to)]
                               [(JmpIf cc label_to) (add-directed-edge! CFG label label_to)]
                               [else 0]))])
                   0))]
            [transposed-CFG (transpose CFG)]
            [toposorted
             (rest (tsort transposed-CFG))] ;; ignore the first element of list which is 'conclusion
            [info (dict-set* info 'tsorted toposorted 'CFG CFG)]
            [_ (set! label->live (make-hash))]
            [_ (dict-set! label->live 'conclusion (set (Reg 'rax) (Reg 'rsp)))]
            [new_blocks (map (lambda (x) (uncover-live-block blocks x)) toposorted)])
       (X86Program info new_blocks))]))

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

(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (let* ([instrs (flatten-one (map (lambda (blck) (Block-instr* (cdr blck))) blocks))]
            [liveness (flatten-one (map get-liveness-from-block blocks))]
            [blocks (map remove-liveness blocks)]
            [edges (map get-interference-edges instrs liveness)]
            [graph (undirected-graph (foldr append '() edges))]
            ;; [info (dict-set info 'conflict-edges edges)]
            [mg (undirected-graph (build-move-graph instrs))]
            [mg-edges (get-edges mg)]
            [info (dict-set* info 'conflicts graph 'move-graph mg 'mg-edges mg-edges)])
       (X86Program info blocks))]))

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

(define (allocate-register-instrs inst_list vtc cth)
 (for/list ([inst inst_list])
   (match inst
     [(Instr op args)
      (Instr op
             (for/list ([arg args])
               (match arg
                 [(Var v) (let* ([color (dict-ref vtc (Var v))] [home (dict-ref cth color)]) home)]
                 [else arg])))]
     [else inst])))

(define (allocate-register-block cur_block vtc cth)
  (match cur_block
    [(cons label (Block info instr_list))
     (cons label (Block info (allocate-register-instrs instr_list vtc cth)))]))

(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (let* ([var-to-color (color_graph (dict-ref info 'conflicts)
                                       (dict-keys (dict-ref info 'locals-types)))]
            [info (dict-set info 'colors var-to-color)]
            [colors (list->set (filter (lambda (x) (>= x 0)) (map cdr var-to-color)))]
            [used_callee
             (map Reg '(rbx r12 r13 r14 r15))] ;; assume we are using all the callee saved registers
            [num_used_callee (set-count used_callee)]
            [color-to-home (get-color-to-home colors num_used_callee)]
            [num_spilled (length (filter (lambda (x) (Deref? (cdr x))) color-to-home))]
            [info (dict-set info 'used_callee used_callee)]
            [info (dict-set info 'num_spilled num_spilled)]
            [info (dict-set info 'homes color-to-home)]
            [info (dict-remove info 'liveness)]
            [new_blocks (map (lambda (x) (allocate-register-block x var-to-color color-to-home))
                             blocks)])
       (X86Program info new_blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; ("partial evaluation" ,pe-Lvar ,interp-Lvar)
  `(("shrink" ,shrink ,interp-Lwhile ,type-check-Lwhile)
    ("uniquify" ,uniquify ,interp-Lwhile ,type-check-Lwhile)
    ("uncover-get!" ,uncover-get! ,interp-Lwhile ,type-check-Lwhile)
    ;; ("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
    ;; ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cwhile)
    ;; ("instruction selection" ,select-instructions ,interp-x86-1)
    ;; ("liveness analysis" ,uncover_live ,interp-x86-1)
    ;; ("build interference" ,build-interference ,interp-x86-1)
    ;; ("allocate registers" ,allocate-registers ,interp-x86-1)
    ;; ("patch instructions" ,patch-instructions ,interp-x86-1)
    ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
    ))
