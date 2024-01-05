(define (problem corridor1-pro)
        (:domain corridor1)
        (:init
               (and
                   (= (loc) 0)
                   (> (leng) 0)
               )
        )
        (:goal
               (and
                   (= (loc) (leng))
               )
       )
)


