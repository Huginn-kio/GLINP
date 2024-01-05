(define (problem mnestvar2)
        (:domain mnestvar2)
        (:init
              (and
                (>= (x1) 0)
                (>= (x2) 0)
              )
        )
        (:goal
              (and
                  (= (x1) 0)
              )
        )
)