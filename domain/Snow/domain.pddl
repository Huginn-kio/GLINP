(define (domain snow_domain)
  (:requirements :typing :fluents)
    (:predicates
      (ond)
     )
      (:functions
        (lend)
        (lenw)
    )
      (:action shoveld
         :parameters ()
         :precondition (and (ond) (> (lend) 0))
         :effect (and (increase (lenw) 1) (decrease (lend) 1))
    )
    (:action shovelw
         :parameters ()
         :precondition (and (> (lenw) 0) (= (lend) 0) (not (ond)))
         :effect (and (decrease (lenw) 1))
    )

    (:action moved
         :parameters ()
         :precondition (and (not (ond)))
         :effect (and (ond))
    )
    (:action movew
         :parameters ()
         :precondition (and (ond))
         :effect (and (not (ond)))
    )
)
