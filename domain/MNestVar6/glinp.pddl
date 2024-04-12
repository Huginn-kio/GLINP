(define (problem mnestvar6)
        (:domain mnestvar6)
        (:init
              (and
                (>= (x1) 0)
                (>= (x2) 0)
                (>= (x3) 0)
                (>= (x4) 0)
                (>= (x5) 0)
                (>= (x6) 0)
              )
        )
        (:goal
              (and
                  (= (x1) 0)
              )
        )
)