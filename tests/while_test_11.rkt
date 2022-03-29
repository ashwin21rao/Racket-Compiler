(let ([x 1])
    (begin
      (let ([y (while (< x 5) (set! x (+ x 1)))]) y)
      (+ x 37)
  ))
