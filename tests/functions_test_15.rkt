(define (dec [x : (Vector Integer)]) : Void 
    (vector-set! x 0 42))

(let ([x (vector 1)])
  (begin 
    (dec x)
    (vector-ref x 0)))
  
