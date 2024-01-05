(define (domain Delivery)
  (:requirements :typing :fluents)
   (:predicates           
            (atd)
		)
(:functions 
    (numd)
    (numc)
    (numt)
    (cap)
)


   (:action loadd
       :parameters ()
       :precondition  (and  (< (numt) (cap))   (atd) (> (numd) 0)
			)                      
       :effect (and 
            (decrease (numd) 1)
            (increase (numt) 1)
            )
   )
 
   (:action unloadc
       :parameters ()
       :precondition  (and   (not (atd)) (> (numt) 0) 			)
       :effect (and  
           (increase (numc) 1) 
          (decrease (numt) 1)
	)
   )


   (:action movec
       :parameters  ()
       :precondition (and  (atd)   )
       :effect (and    (not (atd))))

   (:action moved
       :parameters  ()
       :precondition (and    (not (atd)) )
       :effect (and  (atd)
	))

)
