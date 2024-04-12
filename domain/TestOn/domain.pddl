(define (domain teston)
  (:requirements :typing :fluents)
    (:predicates 
      (stack)
     )
  (:functions
    (nx)
    (ny)
    )
(:action pick-stack
        :parameters ()
        :precondition (and (= (nx) 0)   (= (ny) 0)   (not (stack))    ) 
        :effect (and  (stack)  (increase (ny) 1) ) 
        )
(:action put-unstackX
        :parameters ()
        :precondition (and    (> (nx) 0)) 
        :effect (and   (decrease (nx) 1) ) 
        )
(:action put-unstackY
        :parameters ()
        :precondition (and  (> (ny) 0)) 
        :effect (and   (decrease (ny) 1) ) 
        )

)
