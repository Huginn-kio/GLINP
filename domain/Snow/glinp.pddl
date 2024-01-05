(define (problem snow_problem)
        (:domain snow_domain)
        (:init
            (and
              (ond)
              (>= (lenw) 0)
              (>= (lend) 0)
            )
        )
        (:goal (and
                   (ond)
                   (= (lenw) 0)
                   (= (lend) 0)
               )
        )
)