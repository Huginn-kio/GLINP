(define (problem mnestvar8)
        (:domain mnestvar8)
        (:init
              (and
                    (>= (x1) 0)
                    (>= (x2) 0)
                    (>= (x3) 0)
                    (>= (x4) 0)
                    (>= (x5) 0)
                    (>= (x6) 0)
                    (>= (x7) 0)
                    (>= (x8) 0)
              )
        )
        (:goal
              (and
                  (= (x1) 0)
              )
        )
)