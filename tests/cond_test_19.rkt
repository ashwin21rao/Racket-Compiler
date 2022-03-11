(let ([x (if (> (if (>= 1 1) 8 9) 8) #t #f)])
  (if x
      1
      (let ([a 2])
        (+ a (let ([a 2])
          ( + a (let ([a 2])
            ( + a (let ([a 2])
              ( + a (let ([a 2])
                ( + a (let ([a 2])
                  ( + a (let ([a 2])
                    ( + a (let ([a 2])
                      ( + a (let ([a 2]) ( + a (let ([a 2]) ( + a (let ([a 2]) ( + a (let ([a 2]) a)))))))))))))))))))))))))
