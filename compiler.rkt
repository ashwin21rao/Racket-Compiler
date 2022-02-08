#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
;;(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require racket/trace)
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")

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

;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body) (let* ([new_x (gensym x)] [new_env (dict-set env x new_x)])
                        (Let new_x ((uniquify-exp env) e) ((uniquify-exp new_env) body)))]
      [(Prim op es) (Prim op
                          (for/list ([e es])
                            ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; return atom, list of variables
(define (rco-atom expr)
  (match expr
    [(Var x) (cons (Var x) '())]
    [(Int x) (cons (Int x) '())]
    [(Let x e body) (let* ([new_sym (gensym 'temp)]
                           [new_var (Var new_sym)]
                           [list_1 (list x (rco-exp e))]
                           [list_2 (list new_sym (rco-exp body))]
                           [list_3 (append (list list_1) (list list_2))])
                      (cons new_var list_3))]
    [(Prim 'read '()) (let* ([new_sym (gensym 'temp)]
                             [new_var (Var new_sym)]
                             [new_ele (list new_sym (Prim 'read '()))]
                             ) (cons new_var (list new_ele)))]
    [(Prim op (list exp1 exp2)) (let* ([pair_data_1 (rco-atom exp1)]
                                       [pair_data_2 (rco-atom exp2)]
                                       [atom1 (car pair_data_1)]
                                       [atom2 (car pair_data_2)]
                                       [vs1 (cdr pair_data_1)]
                                       [vs2 (cdr pair_data_2)]
                                       [new_sym (gensym 'temp)]
                                       [new_var (Var new_sym)]
                                       [new_prim (Prim op (list atom1 atom2))]
                                       [new_ele (list new_sym new_prim)]
                                       [new_vs (append vs1 vs2 (list new_ele))])
                                  (cons new_var new_vs))]
    [(Prim op (list exp1)) (let* ([pair_data_1 (rco-atom exp1)]
                                  [atom1 (car pair_data_1)]
                                  [vs1 (cdr pair_data_1)]
                                  [new_sym (gensym 'temp)]
                                  [new_var (Var new_sym)]
                                  [new_prim (Prim op (list atom1))]
                                  [new_ele (list new_sym new_prim)]
                                  [new_vs (append vs1 (list new_ele))])
                             (cons new_var new_vs))]
    ))

(define (gen-lets lst)
  (cond
    [(= 1 (length lst)) (cadar lst)]
    [else (Let (caar lst) (cadar lst) (gen-lets (rest lst)))]))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int x) (Int x)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (gen-lets (cdr (rco-atom (Prim op es))))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; explicate-control : R1 -> C0
;; explicate-tail : Lvar -> C0 tail
(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (let* ([tail (explicate-tail body)] [nt (explicate-assign rhs x tail)]) nt)]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate-tail unhandled case" e)]))

;; explicate_assign : Lvar, Var x, C0 tail -> C0 tail
(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body)
     (let* ([tail (explicate-assign body x cont)] [nt (explicate-assign rhs y tail)]) nt)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate-tail body))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; select-instructions : C0 -> pseudo-x86
(define (convert-to-x86 p)
  (match p
    [(Var x) (Var x)]
    [(Int x) (Imm x)]
    [(Seq x y) (append (convert-to-x86 x) (convert-to-x86 y))]
    [(Assign x (Prim '+ (list a1 a2))) (let* ([instr1 (Instr 'movq (list (convert-to-x86 a1) x))]
                                              [instr2 (Instr 'addq (list (convert-to-x86 a2) x))])
                                         (list instr1 instr2))]
    [(Assign x (Prim '- (list a1 a2))) (let* ([instr1 (Instr 'movq (list (convert-to-x86 a1) x))]
                                              [instr2 (Instr 'subq (list (convert-to-x86 a2) x))])
                                         (list instr1 instr2))]
    [(Assign x (Prim '- (list a1))) (let* ([instr1 (Instr 'movq (list (convert-to-x86 a1) x))]
                                           [instr2 (Instr 'negq (list x))])
                                      (list instr1 instr2))]
    [(Assign x (Prim 'read '())) (let* ([instr1 (Callq 'read_int 0)]
                                        [instr2 (Instr 'movq (list (Reg 'rax) x))])
                                    (list instr1 instr2))]
    [(Assign x y) (let* ([instr1 (Instr 'movq (list (convert-to-x86 y) x))]) (list instr1))]
    [(Return e) (let * ([instrs (convert-to-x86 (Assign (Reg 'rax) e))] [instr2 (Jmp 'conclusion)])
                  (append instrs (list instr2)))]))

(define (select-instructions-block blck)
  (match blck
    [(cons label cmds) (cons label (Block '() (convert-to-x86 cmds)))]
    )
  )
(define (select-instructions p)
  (match p
    [(CProgram info blocks) (X86Program info (map select-instructions-block blocks))]))

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
    [(cons label (Block info instr_list)) (cons label (Block info (assign-home-instr-list instr_list var_stack_mapping)))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (let* ([var_stack_mapping (var-offset-mapping (dict-keys (dict-ref info 'locals-types)) -8)]
                        [new_blocks (map (lambda (x) (assign-homes-blocks x var_stack_mapping)) blocks)])
                   new_blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; patch-instructions : psuedo-x86 -> x86

(define (fix-instructions inst_list)
              (for/list ([inst inst_list])
                (match inst
                  [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
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
     (X86Program info
                 (let* ([stacksize (* 8 (+ 2 (length (dict-keys (dict-ref info 'locals-types)))))]
                        [stacksize (+ stacksize (modulo stacksize 16))]
                        [instr1 (Instr 'pushq (list (Reg 'rbp)))]
                        [instr2 (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))]
                        [instr3 (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))]
                        [instr4 (Jmp 'start)]
                        [instr5 (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))]
                        [instr6 (Instr 'popq (list (Reg 'rbp)))]
                        [instr7 (Retq)]
                        [main_block (Block empty (list instr1 instr2 instr3 instr4))] 
                        [conclusion_block (Block empty (list instr5 instr6 instr7))]
                        [blocks (dict-set* blocks 'main main_block 'conclusion conclusion_block)])
                   blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(("uniquify" ,uniquify ,interp-Lvar)
    ;; Uncomment the following passes as you finish them.
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-x86-0)
    ("assign homes" ,assign-homes ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))
