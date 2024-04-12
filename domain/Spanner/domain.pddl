(define (domain spanner)
  (:requirements :typing :fluents)
  (:predicates
    (empty)
  )

(:functions
    (numn)
    (nums)
    (numc)
    (dist)
)

(:action walk
:parameters  ()
:precondition (and  (> (dist) 0) (empty) )
:effect (and  (decrease (dist) 1) (not (empty)) )
)

(:action pickup
:parameters  ()
:precondition (and  (> (dist) 0) (not (empty)) (> (nums) 0))
:effect (and (empty) (decrease (nums) 1) (increase (numc) 1))
) 

(:action tighten
:parameters  ()
:precondition (and  (= (dist) 0) (> (numc) 0) (> (numn) 0))
:effect (and  (decrease (numn) 1) (decrease (numc) 1))
)

)
