(define (domain visitall)
  (:requirements :typing :fluents)
  (:predicates 
    (visitr)
    (visitl)
  )

(:functions 
    (disr)
    (disl)
    (dist)
    (disb)
    (numr)
)

(:action mover
:parameters  ()
:precondition (and  (> (disr) 0) )
:effect (and  (decrease (disr) 1) (increase (disl) 1)))

(:action movel
:parameters  ()
:precondition (and  (> (disl) 0) )
:effect (and  (decrease (disl) 1) (increase (disr) 1)))

(:action moved
:parameters  ()
:precondition (and (> (disb) 0) (= (disl) 0) (visitr) (visitl))
:effect (and  (decrease (disb) 1) (increase (dist) 1) (not (visitr)) (not (visitl))
  ))             
(:action Markl
:parameters  ()
:precondition (and  (= (disl) 0)  (not (visitl)) (visitr))
:effect (and  (visitl)   (increase (numr) 1)
  ))

(:action Markr
:parameters  ()
:precondition (and  (= (disr) 0)  (not (visitr)) (not (visitl)))
:effect (and  (visitr) 
  ))

)
