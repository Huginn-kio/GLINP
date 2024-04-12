(define (domain mnestvar2)
  (:requirements :typing :fluents)
  (:functions
    (x1)
    (x2)
    )
(:action DecX1
        :parameters ()
        :precondition (and (= (x2) 0)) 
        :effect (and  (decrease (x1) 1)  (assign (x2) (x1)))
        )
(:action DecX2
        :parameters ()
        :precondition (and (> (x2) 0))
        :effect (and (decrease (x2) 1))
        )
)
