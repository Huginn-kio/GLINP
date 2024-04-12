(define (problem nestvar2)
        (:domain nestvar2)
        (:init
              (and
                (>= (x1) 0)
                (>= (x2) 0)
              )
        )
        (:goal
              (and
                  (= (x1) 0)
                  (= (x2) 0)
              )
        )
)