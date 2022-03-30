(let ([n (read)])
  (let ([a 0])
    (let ([b 1])
      (let ([sum 1])
        (let ([c (+ a b)])
          (begin
             (while (> n 0)
                    (begin
                       (set! sum (+ sum c))
                       (set! a b)
                       (set! b c)
                       (set! c (+ a b))
                       (set! n (- n 1))))
             sum))))))
