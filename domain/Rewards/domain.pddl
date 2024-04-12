(define (domain rewards)
  (:requirements :typing :fluents)
  (:functions
    (numr)
    (dis)
    (gap)
    )
(:action collect
        :parameters ()
        :precondition (and (> (numr) 0)  (= (dis) 0)) 
        :effect (and  (decrease (numr) 1)  (assign (dis) (gap)) )
        )
(:action move-to-closest-reward
        :parameters ()
        :precondition (and (> (numr) 0)  (> (dis) 0) )
        :effect (and (decrease (dis) 1))
        )
)
