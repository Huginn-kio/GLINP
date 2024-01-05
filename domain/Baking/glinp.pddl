(define (problem pro-baking)
        (:domain baking)
        (:init
              (and
                (not (inep))
                (not (infp))
                (not (mixed))
                (not (inpo))
                (not (baked))
                (clean)
                (> (numcake) 0)
              )
        )
        (:goal (and
               (= (numcake) 0)
               (clean)
               )
        )
)



