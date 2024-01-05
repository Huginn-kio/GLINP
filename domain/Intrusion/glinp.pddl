(define (problem intrusion1-pro)
        (:domain intrusion1)
        (:init
               (and
                        (= (numcon) 0)
                        (= (numbrk) 0)
                        (= (numcln) 0)
                        (= (numgained) 0)
                        (= (numdown) 0)
                        (= (numstl) 0)
                        (> (numhost) 0)
               )
        )
        (:goal
                (and
                        (= (numstl) (numhost))
                )
       )
)