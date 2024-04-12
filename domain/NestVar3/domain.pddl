(define (domain nestvar3)
  (:requirements :typing :fluents)
  (:functions
    (x)
    (y)
    (z)
    )
(:action DecX
        :parameters ()
        :precondition (and (> (x) 0) (= (y) 0) (= (z) 0)) 
        :effect (and  (decrease (x) 1)  (increase (y) 1)  (increase (z) 1))
        )
(:action DecY
        :parameters ()
        :precondition (and (> (y) 0) (= (z) 0))
        :effect (and (decrease (y) 1)  (increase (z) 1) )
        )
(:action DecZ
        :parameters ()
        :precondition (and (> (z) 0))
        :effect (and (decrease (z) 1))
        )
)
