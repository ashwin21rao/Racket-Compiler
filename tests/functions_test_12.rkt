(define (add [x : (Vector Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer) 
    (vector (vector-ref x 0) (vector-ref x 1) (vector-ref x 2) (vector-ref x 0) (vector-ref x 2) (vector-ref x 1))
  )


(define (pass [f : (Integer -> Integer)]) : (Integer -> Integer)
  f)

(define (inc [x : Integer]) : Integer
    (+ x 1))


(define (len [x : (Vector Integer Integer Integer Integer Integer Integer)]): Integer
    (vector-length x)
  )
((pass inc) (vector-ref (add (vector 1 41 3)) 5))
