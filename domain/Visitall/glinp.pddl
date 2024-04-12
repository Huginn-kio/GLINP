(define (problem pro-visitall)
        (:domain visitall)
        (:init
              (and
                (not (visitr))
                (not (visitl))
                (>= (disr) 0)
                (= (disl) 0)
                (= (dist) 0)
                (>= (disb) 0)
                (= (numr) 0)
              )
        )
        (:goal (and
               (= (numr) (+ (+ (disb) (dist)) 1))
               )
        )
)