(define (add [x : (Vector Integer Integer Integer)]) : (Vector Integer Integer Integer Integer Integer Integer) 
    (vector (vector-ref x 0) (vector-ref x 1) (vector-ref x 2) (vector-ref x 0) (vector-ref x 2) (vector-ref x 1))
  )

(define (len [x : (Vector Integer Integer Integer Integer Integer Integer)]): Integer
    (vector-length x)
  )
(+ 36 (len (add (vector 1 2 3))))
