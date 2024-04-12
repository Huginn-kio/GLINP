(define (problem blocksplace-pro)
        (:domain blocksplace)
        (:init
              (and
                (empty)
                (not (heldX))
                (not (XOnY))
                (> (nx) 0)
                (> (ny) 0)
              )
        )
        (:goal
              (and
                  (XOnY)
              )
        )
)