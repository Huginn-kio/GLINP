(define (domain mnestvar4)
  (:requirements :typing :fluents)
  (:functions
    (x1)
    (x2)
    (x3)
    (x4)
    )
(:action DecX1
        :parameters ()
        :precondition (and  (= (x2) 0) (= (x3) 0) (= (x4) 0) ) 
        :effect (and  (decrease (x1) 1)  (assign (x2) (x1))  (assign (x3) (x1)) (assign (x4) (x1))  )
        )

(:action DecX2
        :parameters ()
        :precondition (and   (= (x3) 0) (= (x4) 0) ) 
        :effect (and  (decrease (x2) 1)  (assign (x3) (x2)) (assign (x4) (x2))  )
        )

(:action DecX3
        :parameters ()
        :precondition (and    (= (x4) 0)  ) 
        :effect (and   (decrease (x3) 1) (assign (x4) (x3))  )
        )

(:action DecX4
        :parameters ()
        :precondition (and   ) 
        :effect (and   (decrease (x4) 1) )
        )

)
