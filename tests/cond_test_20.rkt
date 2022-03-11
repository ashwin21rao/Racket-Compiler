(let ([x (if (> (if (>= 1 1) 8 9) 8) #t #f)])
  (if x
      1
      (let ([a (if (> (read) 1) 1 2)])
        (+ a (let ([a (if (> (read) 1) 1 2)])
          ( + a (let ([a (if (> (read) 1) 1 2)])
            ( + a (let ([a (if (> (read) 1) 1 2)])
              ( + a (let ([a (if (> (read) 1) 1 2)])
                ( + (read) (let ([a (if (> (read) 1) 1 2)])
                  ( + a (let ([a (if (> (read) 1) 1 2)])
                    ( + a (let ([a (if (> (read) 1) 1 2)])
                      ( + a (let ([a (if (> (read) 1) 1 2)]) ( + a (let ([a (read)]) ( + a (let ([a (if (> (read) 1) 1 2)]) ( + a (let ([a (if (> (read) 1) 1 2)]) a)))))))))))))))))))))))))
