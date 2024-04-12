(define (problem arith-pro)
        (:domain arith)
        (:init
               (and
                        (= (v1) 0)
                        (= (v2) 0)
                        (> (n) 0)
               )
        )
        (:goal
                (and
                        (= (v1) (n))
                        (= (v2) (+ (n) (+ (n) 1)))
                )
       )
)
