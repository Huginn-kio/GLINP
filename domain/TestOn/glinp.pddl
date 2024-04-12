(define (problem teston-pro)
        (:domain teston)
        (:init
            (and
              (not (stack))
              (> (nx) 0)
              (> (ny) 0)
            )
        )
        (:goal
              (and
                  (stack)
              )
        )
)