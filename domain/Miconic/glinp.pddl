(define (problem pro-miconic1)
        (:domain miconic1)
        (:init
            (and
              (= (curf) 1)
              (> (topf) 1)
              (> (numf) 0)
              (= (nume) 0)
              (= (numt) 0)
              (> (cap) 0)
            )
        )
        (:goal (and
                   (= (curf) 1)
                   (= (nume) 0)
                   (= (numf) 0)
                )
        )
)

