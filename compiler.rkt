#lang racket
(require racket/set
         racket/stream)
(require racket/dict)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

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

(define (rco-atom expr)
  (match expr
    [(Var x) (list (list (Var x) '()))]
    [(Int x) (list (list (Int x) '()))]
    [(Let x e body) (Let x (rco-exp e)
                      (rco-exp body))]
    [(Prim op (list exp1 exp2)) (let* ([vs1 (rco-atom exp1)]
                                [vs2 (rco-atom exp2)]
                                [atom1 (car (last vs1))]
                                [atom2 (car (last vs2))]
                                [new_var (Var (gensym 'temp))]
                                [new_prim (Prim op (list atom1 atom2))]
                                [new_ele (list new_var new_prim)])
                           (append vs1 vs2 (list new_ele)))]
    [(Prim op (list exp1)) (let* ([vs1 (rco-atom exp1)]
                           [atom1 (car (last vs1))]
                           [new_var (gensym 'temp)]
                           [new_prim (Prim op (list atom1))]
                           [new_ele (list new_var new_prim)])
                      (append vs1 (list new_ele)))]))

;; (+ (+ 42 10) (- 10))
;; ((tmp1, (+ 42 10), (tmp2, (- 10)))) + tmp1 tmp2
#| (define (gen-lets lst) |#
#|   (match lst |#
#|     [(list (list a b)) b] |#
#|     [(list (list a b) ...) (Let a b (gen-lets (rest lst)))] |#
#|   )) |#
;; ((temp, (+ 20 10)))
(require racket/trace)	
(trace-define (gen-lets lst)
  (cond 
    [(= 1 (length lst)) (cadar lst)]
    [else (Let (caar lst) (cdar lst) (gen-lets (rest lst)))]
    ))

(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int x) (Int x)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
    [(Prim op es) (gen-lets (rco-atom (Prim op es)))]))

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
