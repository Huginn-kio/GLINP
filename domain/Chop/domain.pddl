(define (domain chopTree)
  (:requirements :typing :fluents)
  (:functions
    (h)
    )
(:action chop
        :parameters ()
        :precondition (and (> (h) 0)  ) 
        :effect (and   (decrease (h) 1)  ) 
        )
)
