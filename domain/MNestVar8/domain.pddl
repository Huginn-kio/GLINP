(define (domain mnestvar8)
  (:requirements :typing :fluents)
  (:functions
    (x1)
    (x2)
    (x3)
    (x4)
    (x5)
    (x6)
    (x7)
    (x8)
    )
(:action DecX1
        :parameters ()
        :precondition (and  (= (x2) 0) (= (x3) 0) (= (x4) 0) (= (x5) 0) (= (x6) 0) (= (x7) 0) (= (x8) 0)) 
        :effect (and  (decrease (x1) 1)  (assign (x2) (x1))  (assign (x3) (x1)) (assign (x4) (x1)) (assign (x5) (x1)) (assign (x6) (x1)) (assign (x7) (x1)) (assign (x8) (x1)) )
        )

(:action DecX2
        :parameters ()
        :precondition (and   (= (x3) 0) (= (x4) 0) (= (x5) 0) (= (x6) 0) (= (x7) 0) (= (x8) 0)) 
        :effect (and  (decrease (x2) 1)  (assign (x3) (x2)) (assign (x4) (x2)) (assign (x5) (x2)) (assign (x6) (x2)) (assign (x7) (x2)) (assign (x8) (x2)) )
        )

(:action DecX3
        :parameters ()
        :precondition (and    (= (x4) 0) (= (x5) 0) (= (x6) 0) (= (x7) 0) (= (x8) 0)) 
        :effect (and   (decrease (x3) 1) (assign (x4) (x3)) (assign (x5) (x3)) (assign (x6) (x3)) (assign (x7) (x3)) (assign (x8) (x3)) )
        )
(:action DecX4
        :parameters ()
        :precondition (and  (= (x5) 0) (= (x6) 0) (= (x7) 0) (= (x8) 0)) 
        :effect (and   (decrease (x4) 1)  (assign (x5) (x4)) (assign (x6) (x4)) (assign (x7) (x4)) (assign (x8) (x4)) ) 
        )

(:action DecX5
        :parameters ()
        :precondition (and   (= (x6) 0) (= (x7) 0)  (= (x8) 0) ) 
        :effect (and   (decrease (x5) 1)  (assign (x6) (x5)) (assign (x7) (x5)) (assign (x8) (x5)) )
        )

(:action DecX6
        :parameters ()
        :precondition (and    (= (x7) 0)  (= (x8) 0) ) 
        :effect (and   (decrease (x6) 1)   (assign (x7) (x6)) (assign (x8) (x6)) )
        )

(:action DecX7
        :parameters ()
        :precondition (and   (= (x8) 0)) 
        :effect (and   (decrease (x7) 1) (assign (x8) (x7)) )
        )
(:action DecX8
        :parameters ()
        :precondition (and  (> (x8) 0) ) 
        :effect (and   (decrease (x8) 1) )
        )
)
