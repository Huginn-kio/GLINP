(define (domain childsnack)
   (:requirements :typing :fluents)
  (:predicates 
    (atk)
  )

(:functions 
    (numnb)
    (numni)
    (numgb)
    (numgi)
    (numnsk)
    (numgsk)
    (numnst)
    (numgst)
    (numnc)
    (numgc)
)

(:action make-sandwich-normal
:parameters  ()
:precondition (and  (> (numnb) 0) (> (numni) 0) )
:effect (and  (decrease (numnb) 1) (decrease (numni) 1) (increase (numnsk) 1) )
)

(:action make-sandwich-no-gluten
:parameters  ()
:precondition (and  (> (numgb) 0) (> (numgi) 0) )
:effect (and  (decrease (numgb) 1) (decrease (numgi) 1) (increase (numgsk) 1) )
)

(:action put-sandwich-normal-on-tray
:parameters  ()
:precondition (and  (atk) (> (numnsk) 0) )
:effect (and  (decrease (numnsk) 1) (increase (numnst) 1) )
)

(:action put-sandwich-no-gluten-on-tray
:parameters  ()
:precondition (and  (atk) (> (numgsk) 0) )
:effect (and  (decrease (numgsk) 1) (increase (numgst) 1) )
)

(:action movec
       :parameters  ()
       :precondition (and (not (atk)) )
       :effect (and  (atk))
)

(:action moved
       :parameters  ()
       :precondition (and  (atk)   )
       :effect (and    (not (atk)))
)

(:action serve-sandwich-normal
       :parameters  ()
       :precondition (and (not (atk)) (> (numnst) 0) (> (numnc) 0))
       :effect (and   (decrease (numnst) 1) (decrease (numnc) 1))
)

(:action serve-sandwich-no-gluten
       :parameters  ()
       :precondition (and (not (atk)) (> (numgst) 0) (> (numgc) 0))
       :effect (and   (decrease (numgst) 1) (decrease (numgc) 1))
)

)
