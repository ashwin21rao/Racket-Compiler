(let ([x 0])
  (let ([i 0])
      (begin
       (while (< i 42)
           (begin
             (set! i (+ i 1))
             (set! x (+ x 1))
             (void)
             ))
       x)))
