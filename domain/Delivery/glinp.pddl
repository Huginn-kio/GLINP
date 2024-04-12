(define (problem prob-Delivery)
        (:domain Delivery)
        (:init
            (and
                (> (numd) 0)
                (= (numc) 0)
                (= (numt) 0)
                (> (cap)  0)
            )
        )
        (:goal (and
               (atd)
               (= (numd) 0)
               (= (numt) 0)
        )
        )
)
