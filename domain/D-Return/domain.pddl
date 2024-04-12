(define (domain Diagonal-Return)
  (:requirements :typing :fluents)
  (:predicates 
    (visitlt)
    (visitrt)
    (visitrb)
  )

(:functions 
    (disr)
    (disl)
    (dist)
    (disb)
    (startt)
    (startl)
)
       (:action mover
       :parameters  ()
       :precondition (and  (> (disr) 0) )
       :effect (and  (decrease (disr) 1) (increase (disl) 1)
		     ))
       (:action movel
       :parameters  ()
       :precondition (and  (> (disl) 0)  )
       :effect (and  (decrease (disl) 1) (increase (disr) 1)
		     ))
       (:action moveu
       :parameters  ()
       :precondition (and  (> (dist) 0) )
       :effect (and  (decrease (dist) 1) (increase (disb) 1)
		     ))
       (:action moved
       :parameters  ()
       :precondition (and  (> (disb) 0) )
       :effect (and  (decrease (disb) 1) (increase (dist) 1)
		     ))             
       (:action mark_lt
       :parameters  ()
       :precondition (and  (= (disl) 0) (= (dist) 0) (not (visitlt)))
       :effect (and  (visitlt)
		     ))
       (:action mark_rt
       :parameters  ()
       :precondition (and  (= (disr) 0) (= (dist) 0) (visitlt) (not (visitrt)))
       :effect (and  (visitrt)
		     ))
       (:action mark_rb
       :parameters  ()
       :precondition (and  (= (disr) 0) (= (disb) 0) (visitrt) (not (visitrb)))
       :effect (and  (visitrb)
		     )) 
)
