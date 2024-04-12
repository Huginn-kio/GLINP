(define (domain arith)
  (:requirements :typing :fluents)
      (:functions
        (v1)
        (v2)
        (n)
    )

    (:action IncV1
         :parameters ()
         :precondition (and )
         :effect (and (increase (v1) 1))
    )

      (:action IncV2
         :parameters ()
         :precondition (and )
         :effect (and (increase (v2) 1) )
    )
)
