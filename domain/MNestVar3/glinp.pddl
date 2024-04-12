(define (problem mnestvar3)
        (:domain mnestvar3)
        (:init
               (and
                    (>= (x) 0)
                    (>= (y) 0)
                    (>= (z) 0)
               )
        )
        (:goal
              (and
                  (= (x) 0)
              )
        )
)