(define (domain barman)
(:requirements :typing :fluents)
  (:predicates 
    (holding)
    (empty)
    (containIg1)
    (containIg2)
    (containIg3)
    (containIg4)
    (containCt)
  )

 (:functions
    (numg)
    (numig1)
    (numig2)
    (numig3)
    (numig4)
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

(:action pour-ingredient3
       :parameters  ()
       :precondition (and  (holding) (containIg1) (containIg2) (> (numig3) 0))
       :effect (and (containIg3) (decrease (numig3) 1) )
)

(:action pour-ingredient4
       :parameters  ()
       :precondition (and  (holding) (containIg1) (containIg2) (containIg3) (> (numig4) 0))
       :effect (and (containIg4) (decrease (numig4) 1) )
)

(:action clean
       :parameters  ()
       :precondition (and (holding) (not (empty)) (not (containIg1)) (not (containIg2)) (not (containIg3)) (not (containIg4)) (not (containCt)) )
       :effect (and (not (holding)) (empty) )
)


(:action shake
       :parameters  ()
       :precondition (and  (holding) (containIg1) (containIg2) (containIg3) (containIg4))
       :effect (and (not (containIg1)) (not (containIg2)) (not (containIg3)) (not (containIg4)) (containCt) )
)

(:action pour-cocktail-to-glass
       :parameters  ()
       :precondition (and (holding) (> (numg) 0) (containCt) )
       :effect (and (not (containCt)) (decrease (numg) 1) (decrease (numct) 1))
)

)
