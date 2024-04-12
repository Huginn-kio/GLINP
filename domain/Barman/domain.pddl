(define (domain barman)
(:requirements :typing :fluents)
  (:predicates 
    (holding)
    (empty)
    (containIg1)
    (containIg2)
    (containCt)
  )

 (:functions
    (numg)
    (numig1)
    (numig2)
    (numct)
)

(:action pick-up-shaker
       :parameters  ()
       :precondition (and  (not (holding)) )
       :effect (and (holding) )
)

(:action pour-ingredient1
       :parameters  ()
       :precondition (and  (holding) (empty) (> (numig1) 0))
       :effect (and (not (empty)) (containIg1) (decrease (numig1) 1) )
)

(:action pour-ingredient2
       :parameters  ()
       :precondition (and  (holding) (containIg1) (> (numig2) 0))
       :effect (and (containIg2) (decrease (numig2) 1) )
)

(:action clean
       :parameters  ()
       :precondition (and (holding) (not (empty)) (not (containIg1)) (not (containIg2)) (not (containCt)) )
       :effect (and (not (holding)) (empty) )
)


(:action shake
       :parameters  ()
       :precondition (and  (holding) (containIg1) (containIg2) )
       :effect (and (not (containIg1)) (not (containIg2)) (containCt) )
)

(:action pour-cocktail-to-glass
       :parameters  ()
       :precondition (and (holding) (> (numg) 0) (containCt) )
       :effect (and (not (containCt)) (decrease (numg) 1) (decrease (numct) 1))
)

)
