(define (problem rewards)
        (:domain rewards)
        (:init
              (and
                (> (numr) 0)
                (> (dis) 0)
                (> (gap) 0)
              )
        )
        (:goal
              (and
                  (= (numr) 0)
              )
        )
)