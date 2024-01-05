(define (problem strips-gripper-x-1)
        (:domain gripper-strips)
        (:init
              (and
                    (>  (na) 0)
                    (=  (nb) 0)
                    (=  (mc) 0)
                    (>  (me) 0)
              )
        )
        (:goal (and
                   (la)
                   (=  (na) 0)
                   (>  (nb) 0)
                   (=  (mc) 0)
                   (>  (me) 0)
                )
        )
)