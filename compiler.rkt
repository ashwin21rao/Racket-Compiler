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

#| (define (uniquify-exp env) |#
#|   (lambda (e) |#
#|     (match e |#
#|       [(Var x) (Var x)] |#
#|       [(Int n) (Int n)] |#
#|       [(Let x e body) (Let x ((uniquify-exp env) e) ((uniquify-exp env) body))] |#
#|       [(Prim op es) (Prim op |#
#|                           (for/list ([e es]) |#
#|                             ((uniquify-exp env) e)))]))) |#

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

;; remove-complex-opera* : R1 -> R1

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

;; (+ (+ 42 10) (- 10))
;; ((tmp1, (+ 42 10), (tmp2, (- 10)))) + tmp1 tmp2
#| (define (gen-lets lst) |#
#|   (match lst |#
#|     [(list (list a b)) b] |#
#|     [(list (list a b) ...) (Let a b (gen-lets (rest lst)))] |#
#|   )) |#
;; ((temp, (+ 20 10)))
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

(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;; explicate-control : R1 -> C0
;; explicate_tail : Lvar -> C0 tail
(define (explicate_tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (let* ([tail (explicate_tail body)] [nt (explicate_assign rhs x tail)]) nt)]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate_tail unhandled case" e)]))

;; explicate_assign : Lvar, Var x, C0 tail -> C0 tail
(define (explicate_assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body)
     (let* ([tail (explicate_assign body x cont)] [nt (explicate_assign rhs y tail)]) nt)]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate_assign unhandled case" e)]))

(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate_tail body))))]))

;; select-instructions : C0 -> pseudo-x86
;; TODO implement read too
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
    [(Assign x y) (let* ([instr1 (Instr 'movq (list (convert-to-x86 y) x))]) (list instr1))]
    [(Return e) (let * ([instrs (convert-to-x86 (Assign (Reg 'rax) e))] [instr2 (Jmp 'conclusion)])
                  (append instrs (list instr2)))]))

(define (select-instructions p)
  (match p
    [(CProgram info blocks)
     (X86Program info (list (cons 'start (Block '() (convert-to-x86 (dict-ref blocks 'start))))))]))

(define (set_variable var_list position)
  (cond
    [(empty? var_list) (list)]
    [else (cons (list (car var_list) position) (set_variable (cdr var_list) (- position 8)))]))

(define (replace_inst_list inst_list var_list)
  (for/list ([inst inst_list])
    (match inst
      [(Instr op args) (Instr op
                              (for/list ([arg args])
                                (match arg
                                  [(Var v) (Deref 'rbp (first (dict-ref var_list v)))]
                                  [else arg])))]
      [else inst])))

(define (replace_vars cur_block var_list)
  (match cur_block
    [(Block info inst_list) (Block info (replace_inst_list inst_list var_list))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (let* ([var_list (set_variable (dict-keys (dict-ref info 'locals-types)) -8)]
                        [new_p (replace_vars (dict-ref blocks 'start) var_list)])
                   (dict-set blocks 'start new_p)))]))
; (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86

(trace-define (fix-instructions inst_list)
              (for/list ([inst inst_list])
                (match inst
                  [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
                   (let* ([instr1 (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))]
                          [instr2 (Instr op (list (Reg 'rax) (Deref reg2 off2)))])
                     (list instr1 instr2))]
                  [else inst])))

(trace-define (patch-block pr)
              (cons (car pr)
                    (match (cdr pr)
                      [(Block info instrs) (Block info (flatten (fix-instructions instrs)))]
                      [else
                       error
                       "Not a valid block"])))

(trace-define (patch-instructions p)
              (match p
                [(X86Program info blocks) (X86Program info (map patch-block blocks))]))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (X86Program info
                 (let* ([stacksize (* 8 (length (dict-keys (dict-ref info 'locals-types))))]
                        [instr1 (Instr 'pushq (list (Reg 'rbp)))]
                        [instr2 (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))]
                        [instr3 (Instr 'subq (list (Imm stacksize) (Reg 'rsp)))]
                        [instr4 (Jmp 'start)]
                        [instr5 (Instr 'addq (list (Imm stacksize) (Reg 'rsp)))]
                        [instr6 (Instr 'popq (list (Reg 'rbp)))]
                        [instr7 (Retq)]
                        [main_block (Block empty (list instr1 instr2 instr3 instr4))] 
                        [conclusion_block (Block empty (list instr5 instr6 instr7))])
                   (dict-set* blocks 'main main_block 'conclusion conclusion_block)))]))

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
