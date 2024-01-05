(define (domain Corner-A)
  (:requirements :typing :fluents)
(:functions 
    (disr)
    (disl)
    (dist)
    (disb)
)

       (:action mover
       :parameters  ( )
       :precondition (and  (> (disr) 0) )
       :effect (and  (decrease (disr) 1) (increase (disl) 1)
		     ))
       (:action movel
       :parameters  ()
       :precondition (and  (> (disl) 0) )
       :effect (and  (decrease (disl) 1) (increase (disr) 1)
		     ))
       (:action moveu
       :parameters  ()
       :precondition (and  (> (dist) 0))
       :effect (and  (decrease (dist) 1) (increase (disb) 1)
		     ))
       (:action moved
       :parameters  ()
       :precondition (and  (> (disb) 0))
       :effect (and  (decrease (disb) 1) (increase (dist) 1)
		     ))             

)
