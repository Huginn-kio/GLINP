(define (domain blocksplace)
  (:requirements :typing :fluents)
    (:predicates 
      (empty)
      (heldX)
      (XOnY)
     )
  (:functions
    (nx)
    (ny)
    )
(:action pickAboveX
        :parameters ()
        :precondition (and (empty)  (not (heldX)) (not (XOnY)) (> (nx) 0) (> (ny) 0)) 
        :effect (and  (not (empty))  (decrease (nx) 1) ) 
        )
(:action pickAboveY
        :parameters ()
        :precondition (and (empty)  (not (heldX)) (not (XOnY)) (= (nx) 0) (> (ny) 0)) 
        :effect (and  (not (empty))  (decrease (ny) 1) ) 
        )
(:action put-aside-1
        :parameters ()
        :precondition (and  (not (empty))  (not (heldX))   (not (XOnY)) (= (nx) 0)) 
        :effect (and   (empty) ) 
        )

(:action put-aside-2
        :parameters ()
        :precondition (and  (not (empty))  (not (heldX))   (not (XOnY))     (> (nx) 0)   (> (ny) 0)) 
        :effect (and   (empty) ) 
        )

(:action pick-x
        :parameters ()
        :precondition (and   (empty)  (not (heldX))   (not (XOnY))     (= (nx) 0)   (= (ny) 0)) 
        :effect (and   (heldX)    (not (empty))) 
        )
(:action put-x-aside
        :parameters ()
        :precondition (and   (heldX)  (not (empty))   (not (XOnY))     (= (nx) 0)   (> (ny) 0)) 
        :effect (and   (empty)    (not (heldX))) 
        )
(:action put-x-on-y
        :parameters ()
        :precondition (and   (heldX)  (not (empty))   (not (XOnY))     (= (nx) 0)   (= (ny) 0)) 
        :effect (and   (empty)    (not (heldX))  (XOnY)  (increase (ny) 1)) 
        )
)
