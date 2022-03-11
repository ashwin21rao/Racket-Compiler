(if (eq? (read) (read)) (let ([x 1]) x) (let ([x (if (>= 1 1) (let ([x (> 5 5)]) (not x)) (let ([x (< 5 5)]) x))]) (+ (read) (if x 1 2))))
