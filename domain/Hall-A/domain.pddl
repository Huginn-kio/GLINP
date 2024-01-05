(define (domain Hall-A)
  (:requirements :typing :fluents)

  (:predicates 
    (visitlt)
    (visitrt)
    (visitlb)
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
       :precondition (and  (or(= (dist) 0) (= (disb) 0)))
       :effect (and  (decrease (disr) 1) (increase (disl) 1)
		     ))
       (:action movel
       :parameters  ()
       :precondition (and  (or (= (dist) 0) (= (disb) 0)))
       :effect (and  (decrease (disl) 1) (increase (disr) 1)
		     ))
       (:action moveu
       :parameters  ()
       :precondition (and  (or (= (disr) 0) (= (disl) 0)))
       :effect (and  (decrease (dist) 1) (increase (disb) 1)
		     ))
       (:action moved
       :parameters  ()
       :precondition (and  (or (= (disr) 0) (= (disl) 0)))
       :effect (and  (decrease (disb) 1) (increase (dist) 1)
		     ))             
       (:action mark_rb
       :parameters  ()
       :precondition (and  (= (disr) 0) (= (disb) 0) (not (visitrb)))
       :effect (and  (visitrb)
		     ))
       (:action mark_lb
       :parameters  ()
       :precondition (and  (= (disl) 0) (= (disb) 0) (visitrb) (not (visitlb)))
       :effect (and  (visitlb)
		     ))
      (:action mark_lt
       :parameters  ()
       :precondition (and  (= (disl) 0) (= (dist) 0) (visitlb) (not (visitlt)) )
       :effect (and  (visitlt)
		     ))
        (:action mark_rt
       :parameters  ()
       :precondition (and  (= (disr) 0) (= (dist) 0) (visitlt) (not (visitrt)))
       :effect (and  (visitrt)
		     ))                  
)
