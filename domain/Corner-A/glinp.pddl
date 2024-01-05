(define (problem pro-Corner-A)
        (:domain Corner-A)
        (:init
              (and
                (>= (disr) 0)
                (>= (disl) 0)
                (>= (dist) 0)
                (>= (disb) 0)
              )
        )
        (:goal (and
                   (= (disr) 0)
                   (= (dist) 0)
               )
        )
)