#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
(require graph)
;;(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require "priority_queue.rkt")
(require "heap.rkt")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Partial evaluation for Lvar language
;; TODO change partial evaluation in the other branch too
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
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; HW1 Passes ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;; return cons(atom, (list (cons variables exp)))
(define (rco-atom expr)
  (match expr
    [(Var x) (cons (Var x) '())]
    [(Int x) (cons (Int x) '())]
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
    [(Prim 'read '()) (Prim 'read '())]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (gen-lets (cdr (rco-atom (Prim op es))))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body) (CProgram info (list (cons 'start (explicate-tail body))))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; select-instructions-atom: C0 atom -> pseudo-x86 atom
(define (select-instructions-atm atm)
  (match atm
    [(Var x) (Var x)]
    [(Int x) (Imm x)]
    [else (error "Unhandled atom in select instructions" atm)]))

(define (select-instructions-exp p)
  (match p
    [(Seq x y) (append (select-instructions-exp x) (select-instructions-exp y))]
    [(Assign x (Prim '+ (list a1 a2)))
     (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
            [instr2 (Instr 'addq (list (select-instructions-atm a2) x))])
       (list instr1 instr2))]
    [(Assign x (Prim '- (list a1 a2)))
     (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
            [instr2 (Instr 'subq (list (select-instructions-atm a2) x))])
       (list instr1 instr2))]
    [(Assign x (Prim '- (list a1)))
     (let* ([instr1 (Instr 'movq (list (select-instructions-atm a1) x))]
            [instr2 (Instr 'negq (list x))])
       (list instr1 instr2))]
    [(Assign x (Prim 'read '())) (let* ([instr1 (Callq 'read_int 0)]
                                        [instr2 (Instr 'movq (list (Reg 'rax) x))])
                                   (list instr1 instr2))]
    [(Assign x y) (let* ([instr1 (Instr 'movq (list (select-instructions-atm y) x))]) (list instr1))]
    [(Return e)
     (let * ([instrs (select-instructions-exp (Assign (Reg 'rax) e))] [instr2 (Jmp 'conclusion)])
       (append instrs (list instr2)))]))

(define (select-instructions-block blck)
  (match blck
    [(cons label cmds) (cons label (Block '() (select-instructions-exp cmds)))]))

;; select-instructions : C0 -> pseudo-x86
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
(define (filter-var-reg lst)
  (list->set (filter (lambda (x) (or (Var? x) (Reg? x))) lst)))

(define (instr-location-read instr)
  (let* ([live_list (match instr
                      [(Instr 'movq (list arg1 arg2)) (list arg1)]
                      [(Instr 'addq (list arg1 arg2)) (list arg1 arg2)]
                      [(Instr 'subq (list arg1 arg2)) (list arg1 arg2)]
                      [(Instr 'negq (list arg1)) (list arg1)]
                      [(Callq x y) (map Reg
                                        (take '(rdi rsi rdx rcx r8 r9)
                                              y))] ;; TODO what happens if more than 6 args
                      [(Jmp label) empty]
                      [else (error "Invalid instruction" instr)])]
         [filter_list (filter (lambda (x) (or (Var? x) (Reg? x))) live_list)])
    (list->set filter_list)))

(define (instr-location-written instr)
  (let* ([live_list (match instr
                      [(Instr op es) (list (last es))]
                      [(Callq x y)
                       (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11))] ;; make these actual registers
                      [(Jmp label) empty]
                      [else (error "Invalid instruction" instr)])]
         [filter_list (filter (lambda (x) (or (Var? x) (Reg? x))) live_list)])
    (list->set filter_list)))

(define (uncover-live-instrs instrs prev_liveness)
  (match instrs
    [(list) empty]
    [else
     (let* ([instr (first instrs)]
            [prev_liveness (match instr
                             [(Jmp label) (set (Reg 'rax) (Reg 'rsp))]
                             [else prev_liveness])]
            [locations_read (instr-location-read instr)]
            [locations_written (instr-location-written instr)]
            [new_liveness (set-union (set-subtract prev_liveness locations_written) locations_read)])
       (append (uncover-live-instrs (rest instrs) new_liveness) (list new_liveness)))]))

(define (uncover-live-block blck)
  (match blck
    [(cons label (Block info instrs))
     (cons label
           (Block (dict-set info 'liveness (uncover-live-instrs (reverse instrs) (list (set))))
                  instrs))]))

(define (uncover_live p)
  (match p
    [(X86Program info blocks) (X86Program info (map uncover-live-block blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-edges instr_k l_after)
  (let* ([var_written (match instr_k
                        [(Instr 'movq es) (filter-var-reg es)]
                        [else (instr-location-written instr_k)])]
         [l_left (set-subtract l_after var_written)] ;; remove both d, s from l_after
         [l_left_list (set->list l_left)]
         [var_written_list (set->list var_written)]
         [var_written_list
          (match instr_k
            [(Instr 'movq es) (list (last es))] ;; incase of movq only make edges from the dest
            [else var_written_list])] ;; make edges from all the written variables
         [edges (cartesian-product var_written_list l_left_list)])
    edges))

(define (flatten-one lst)
  (foldr append '() lst))

(define (get-liveness-from-block blck)
  (let* ([info (Block-info (cdr blck))]
         [liveness (dict-ref info 'liveness)]
         [liveness (append (cdr liveness) (list (set)))])
    liveness))

(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (let* ([instrs (flatten-one (map (lambda (blck) (Block-instr* (cdr blck))) blocks))]
            [liveness (flatten-one (map get-liveness-from-block blocks))]
            [edges (map get-edges instrs liveness)]
            [graph (undirected-graph (foldr append '() edges))]
            [info (dict-set info 'conflict-edges edges)]
            [info (dict-set info 'conflicts graph)])
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

(define (update-saturation handle color)
  (let* ([var (get-var handle)]
         [saturation (get-sat handle)]
         [new_sat (set-union saturation (set color))])
    (set-node-key! handle (cons var new_sat))))

(define (update-saturations graph handles var color)
  (let* ([neighbours (sequence->list (in-neighbors graph var))]
         [neighbour-handles (filter (lambda (x) (find-handle-neigh x neighbours)) handles)]
         [_ (map (lambda (x) (update-saturation x color)) neighbour-handles)])
    color))

(define (get_greedy_color sat_popped num)
  (if (set-member? sat_popped num) (get_greedy_color sat_popped (+ num 1)) num))

(define (not-while-loop n graph handles w)
  (cond
    [(= n 0) '()]
    [else (let* ([node_popped (pqueue-pop! w)]
                 [var_popped (car node_popped)]
                 [sat_popped (cdr node_popped)]
                 [reqd_color (get_greedy_color sat_popped 0)]
                 [color_pair (cons (Var var_popped) reqd_color)]
                 [handles (filter (lambda (x) (not (equal? (car (node-key x)) var_popped)))
                                  handles)] ;; remove the popped element from handles
                 [_ (update-saturations graph handles (Var var_popped) reqd_color)]
                 [lst (append (list color_pair) (not-while-loop (- n 1) graph handles w))])
            lst)]))

(define (color_graph graph vars)
  (let* ([var_color (list (cons (Reg 'rax) -1) (cons (Reg 'rsp) -2))]
         [w (make-pqueue saturation-cmp)]
         [handles (for/list ([var vars])
                    (pqueue-push! w (cons var (set))))]
         [call1 (update-saturations graph handles (Reg 'rax) -1)]
         [call2 (update-saturations graph handles (Reg 'rsp) -2)]
         [n (pqueue-count w)]
         [vars (not-while-loop n graph handles w)]
         [var_color (append var_color vars)])
    var_color))

(define (get-color-to-home reg_list current_color max_color offset)
  (cond
    [(> current_color max_color) '()]
    [(empty? reg_list)
     (let* ([current_map (cons current_color (Deref 'rbp offset))]
            [current_map
             (append (list current_map)
                     (get-color-to-home reg_list (+ 1 current_color) max_color (- offset 8)))])
       current_map)]
    [else (let* ([current_map (cons current_color (car reg_list))]
                 [current_map
                  (append (list current_map)
                          (get-color-to-home (rest reg_list) (+ 1 current_color) max_color offset))])
            current_map)]))

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
            [reg_list (map Reg '(rcx))]
            [max_color (foldl (lambda (x y) (max (cdr x) y)) 0 var-to-color)]
            [color-to-home (get-color-to-home reg_list 0 max_color -8)]
            [info (dict-set info 'homes color-to-home)]
            [new_blocks
             (map (lambda (x) (allocate-register-block x var-to-color color-to-home)) blocks)])
       (X86Program info new_blocks))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  ;; ("partial evaluation" ,pe-Lvar ,interp-Lvar)
  `(("uniquify" ,uniquify ,interp-Lvar)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
    ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
    ("instruction selection" ,select-instructions ,interp-x86-0)
    ("liveness analysis" ,uncover_live ,interp-x86-0)
    ("build interference" ,build-interference ,interp-x86-0)
    ("allocate registers" ,allocate-registers ,interp-x86-0)
    ("patch instructions" ,patch-instructions ,interp-x86-0)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)))
