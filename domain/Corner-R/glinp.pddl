(define (problem pro-Corner-R)
        (:domain corn-R)
        (:init
                (and
                    (dectr)
                    (not (dectl))
                    (not (dectt))
                    (not (dectb))
                    (>= (disr) 0)
                    (>= (disl) 0)
                    (>= (dist) 0)
                    (>= (disb) 0)
                )
        )
        (:goal (and
                   (= (disr) 0)
                   (= (dist) 0)
               )
        )
)