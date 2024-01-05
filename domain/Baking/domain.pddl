(define (domain baking)
(:requirements :typing :fluents)

  (:predicates
    (inep)
    (infp)
    (mixed)
    (inpo)
    (baked)
    (clean)
  )

(:functions
    (numcake)

)

(:action poure
       :parameters  ()
       :precondition (and (> (numcake) 0) (clean) (not (inep)))
       :effect (and  (not (clean)) (inep))
)

(:action pourf
       :parameters  ()
       :precondition (and  (inep) (not (infp)))
       :effect (and (infp) )
)

(:action mix
       :parameters  ()
       :precondition (and  (inep) (infp) (not (mixed)))
       :effect (and  (mixed) (not (inep)) (not (infp)))
)

(:action put
       :parameters  ()
       :precondition (and (not (inpo)) (mixed))
       :effect (and  (inpo) (not (mixed)))
)

(:action bake
       :parameters  ()
       :precondition (and  (inpo) (not (baked)))
       :effect (and (baked))
)

(:action takeout
       :parameters  ()
       :precondition (and  (inpo) (baked))
       :effect (and (not (inpo)) (decrease (numcake) 1))
)

(:action cleanpan
       :parameters  ()
       :precondition (and  (not (clean)) (not (inpo)) (baked))
       :effect (and (clean) (not (baked)))
)
)


