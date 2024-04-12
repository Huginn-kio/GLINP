(define (domain nestvar6)
  (:requirements :typing :fluents)
  (:functions
    (x1)
    (x2)
    (x3)
    (x4)
    (x5)
    (x6)
    )
(:action DecX1
        :parameters ()
        :precondition (and (> (x1) 0) (= (x2) 0) (= (x3) 0) (= (x4) 0) (= (x5) 0) (= (x6) 0) ) 
        :effect (and  (decrease (x1) 1)  (increase (x2) 1)  (increase (x3) 1) (increase (x4) 1) (increase (x5) 1) (increase (x6) 1) )
        )

(:action DecX2
        :parameters ()
        :precondition (and  (> (x2) 0) (= (x3) 0) (= (x4) 0) (= (x5) 0) (= (x6) 0) ) 
        :effect (and  (decrease (x2) 1)  (increase (x3) 1) (increase (x4) 1) (increase (x5) 1) (increase (x6) 1)  )
        )

(:action DecX3
        :parameters ()
        :precondition (and   (> (x3) 0) (= (x4) 0) (= (x5) 0) (= (x6) 0) ) 
        :effect (and   (decrease (x3) 1) (increase (x4) 1) (increase (x5) 1) (increase (x6) 1) )
        )
(:action DecX4
        :parameters ()
        :precondition (and   (> (x4) 0) (= (x5) 0) (= (x6) 0)  )
        :effect (and   (decrease (x4) 1)  (increase (x5) 1) (increase (x6) 1)  )
        )

(:action DecX5
        :parameters ()
        :precondition (and   (> (x5) 0) (= (x6) 0) ) 
        :effect (and   (decrease (x5) 1)  (increase (x6) 1))
        )

(:action DecX6
        :parameters ()
        :precondition (and   (> (x6) 0)) 
        :effect (and   (decrease (x6) 1) )
        )
)
