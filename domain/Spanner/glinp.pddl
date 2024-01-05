(define (problem probspanner)
        (:domain spanner)
        (:init
            (and
              (not (empty))
              (> (numn) 0)
              (> (nums) 0)
              (= (numc) 0)
              (> (dist) 0)
              (= (dist) (nums))
              (>= (nums) (numn))
            )
        )
        (:goal (and
                   (= (numn) 0)
                   (= (dist) 0)
                )
        )
)