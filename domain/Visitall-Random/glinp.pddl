(define (problem pro-visitall-Random)
        (:domain visitall-Random)
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
               (= (numr) (+ (disb) (dist)))
               )
        )
)