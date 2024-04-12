(define (domain blockclear)
  (:requirements :typing :fluents)
    (:predicates 
      (empty)
     )
  (:functions
    (n)
    )
(:action put
        :parameters ()
        :precondition (and  (not (empty)))
        :effect (and  (empty))
        )
(:action pick
        :parameters ()
        :precondition (and (empty)   (> (n) 0))
        :effect (and   (not (empty))    (decrease (n) 1))
        )

)
