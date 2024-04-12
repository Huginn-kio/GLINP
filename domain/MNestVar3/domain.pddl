(define (domain mnestvar3)
  (:requirements :typing :fluents)
  (:functions
    (x)
    (y)
    (z)
    )
(:action DecX
        :parameters ()
        :precondition (and (= (y) 0) (= (z) 0)) 
        :effect (and  (decrease (x) 1)  (assign (y) (x))  (assign (z) (x)) )
        )
(:action DecY
        :parameters ()
        :precondition (and (= (z) 0))
        :effect (and (decrease (y) 1)  (assign (z) (y)))
        )
(:action DecZ
        :parameters ()
        :precondition (and (> (z) 0))
        :effect (and (decrease (z) 1))
        )
)
