(define (problem hiking2-pro)
        (:domain hiking2)
        (:init
               (and
                (not (tentup))
                (not (athn))
                (not (atwn))
                (not (attn))
                (not (traveled))
                (energetic)
                (> (numsight) 0)
               )
        )
        (:goal
               (and
                   (= (numsight) 0)
               )
       )
)


