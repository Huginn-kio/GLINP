(define (problem nestvar5)
        (:domain nestvar5)
        (:init
              (and
                (>= (x1) 0)
                (>= (x2) 0)
                (>= (x3) 0)
                (>= (x4) 0)
                (>= (x5) 0)
              )
        )
        (:goal
              (and
                  (= (x1) 0)
                  (= (x2) 0)
                  (= (x3) 0)
                  (= (x4) 0)
                  (= (x5) 0)
              )
        )
)