(define (domain corridor1)
  (:requirements :typing :fluents)
   (:functions
    (loc)
    (leng)
   )
   (:action movel
       :parameters  ()
       :precondition (and (> (loc) 0))
       :effect (and (decrease (loc) 1)
	))

   (:action mover
       :parameters  ()
       :precondition (and (< (loc) (leng)))
       :effect (and (increase (loc) 1)
	))
)
