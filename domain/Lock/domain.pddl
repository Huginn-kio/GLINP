(define (domain lock1)
  (:requirements :typing :fluents)
  (:predicates
    (gotk)
    (opened)
  )
(:functions
    (loc)
    (mid)
    (xkey)
)

(:action movel
:parameters  ()
:precondition (and  (> (loc) 0) (gotk))
:effect (and (decrease (loc) 1) )
)

(:action mover
:parameters  ()
:precondition (and  (< (loc) (xkey)) (not (gotk)))
:effect (and (increase (loc) 1) )
)

(:action pick
:parameters  ()
:precondition (and  (= (loc) (xkey)) (not (gotk)))
:effect (and  (gotk) )
)

(:action unlock
:parameters  ()
:precondition (and  (= (loc) 0) (gotk) (not (opened)))
:effect (and  (opened))
)

)
