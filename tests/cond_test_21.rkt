(let ([x (if (> (if (>= 1 1) 8 9) 8) #t #f)])
  (if x
      1
      (let ([a (if (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) #t #f) 1 2)])
        (+ a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
          ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
            ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
              ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
                ( + (read) (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
                  ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
                    ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)])
                      ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)]) ( + a (let ([a (read)]) ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)]) ( + a (let ([a (if (if (> (read) 1) (let ([a #t]) a) (let ([a #f]) a)) 1 2)]) a)))))))))))))))))))))))))
