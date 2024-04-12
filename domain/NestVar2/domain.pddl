(define (domain nestvar2)
  (:requirements :typing :fluents)
  (:functions
    (x1)
    (x2)
    )
(:action DecX1
        :parameters ()
        :precondition (and (> (x1) 0) (= (x2) 0)) 
        :effect (and  (decrease (x1) 1)  (increase (x2) 1) )
        )
(:action DecX2
        :parameters ()
        :precondition (and (> (x2) 0))
        :effect (and (decrease (x2) 1) )
        )
)
