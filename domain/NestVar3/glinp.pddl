(define (problem nestvar3)
        (:domain nestvar3)
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
                  (= (y) 0)
                  (= (z) 0)
              )
        )
)