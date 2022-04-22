(define (add [x : (Vector Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer) 
    (vector (vector-ref x 0) (vector-ref x 1) (vector-ref x 2) (vector-ref x 0) (vector-ref x 2) (vector-ref x 1))
  )


(define (pass [x : Integer] [f : (Integer -> Integer)] [g : (Integer -> Integer)]) : (Integer -> Integer)
  (if (eq? x 1) f g))

(define (inc [x : Integer]) : Integer
    (+ x 1))

(define (dec [x : Integer]) : Integer
    (- x 1))

(define (len [x : (Vector Integer Integer Integer Integer Integer Integer)]): Integer
    (vector-length x)
  )
((pass 1 inc inc) (vector-ref (add (vector 1 41 3)) 5))
