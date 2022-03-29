(let ([x 50]) (begin (while (>= x 0) (begin (set! x (- x 1)) 42)) 42))
