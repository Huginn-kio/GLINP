(define (domain gripper-strips)
  (:requirements :typing :fluents)
   (:predicates (la)
   )    
    (:functions 
    (na)
    (nb)
    (mc)
    (me)
    )
   (:action moveA
       :parameters  ()
       :precondition (and  (not (la)))
       :effect (and  (la)
		     ))

   (:action moveB
       :parameters  ()
       :precondition (and  (la))
       :effect (and 
		     (not (la))))

   (:action pickA
       :parameters ()
       :precondition  (and  (la)
			    (> (na) 0) 
			 (> (me) 0) 
                         )
       :effect (and 
            (decrease (na) 1)
	    (decrease (me) 1)
	    (increase (mc) 1)
            ))

   (:action dropB
       :parameters ()
       :precondition  (and  (not (la))
			 (> (mc) 0) 
                         )
       :effect (and 
            (increase (nb) 1)
	    (increase (me) 1)
	    (decrease (mc) 1)
            ))

)
