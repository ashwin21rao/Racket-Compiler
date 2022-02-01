#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require racket/trace)

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
(trace-define (rco-atom expr)
              (match expr
                [(Var x) (cons (Var x) '())]
                [(Int x) (cons (Int x) '())]
                [(Let x e body)
                 (let* ([new_var (Var (gensym 'temp))]
                        [list_1 (list x (rco-exp e))]
                        [list_2 (list new_var (rco-exp body))]
                        [list_3 (append (list list_1) (list list_2))])
                    (cons new_var list_3))]
                [(Prim op (list exp1 exp2)) (let* ([pair_data_1 (rco-atom exp1)]
                                                   [pair_data_2 (rco-atom exp2)]
                                                   [atom1 (car pair_data_1)]
                                                   [atom2 (car pair_data_2)]
                                                   [vs1 (cdr pair_data_1)]
                                                   [vs2 (cdr pair_data_2)]
                                                   [new_var (Var (gensym 'temp))]
                                                   [new_prim (Prim op (list atom1 atom2))]
                                                   [new_ele (list new_var new_prim)]
                                                   [new_vs (append vs1 vs2 (list new_ele))])
                                              (cons new_var new_vs))]
                [(Prim op (list exp1)) (let* ([pair_data_1 (rco-atom exp1)]
                                              [atom1 (car pair_data_1)]
                                              [vs1 (cdr pair_data_1)]
                                              [new_var (Var (gensym 'temp))]
                                              [new_prim (Prim op (list atom1))]
                                              [new_ele (list new_var new_prim)]
                                              [new_vs (append vs1 (list new_ele))])
                                         (cons new_var new_vs))]))

;; (+ (+ 42 10) (- 10))
;; ((tmp1, (+ 42 10), (tmp2, (- 10)))) + tmp1 tmp2
#| (define (gen-lets lst) |#
#|   (match lst |#
#|     [(list (list a b)) b] |#
#|     [(list (list a b) ...) (Let a b (gen-lets (rest lst)))] |#
#|   )) |#
;; ((temp, (+ 20 10)))
(trace-define (gen-lets lst)
              (cond
                [(= 1 (length lst)) (cadar lst)]
                [else (Let (caar lst) (cadar lst) (gen-lets (rest lst)))]))

(trace-define (rco-exp e)
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
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(("uniquify" ,uniquify ,interp-Lvar)
    ;; Uncomment the following passes as you finish them.
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
    ;; ("explicate control" ,explicate-control ,interp-Cvar)
    ;; ("instruction selection" ,select-instructions ,interp-x86-0)
    ;; ("assign homes" ,assign-homes ,interp-x86-0)
    ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
    ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
    ))
