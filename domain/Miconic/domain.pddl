(define (domain miconic1)
  (:requirements :typing :fluents)

(:functions
    (curf)
    (topf)
    (numf)
    (numt)
    (nume)
    (cap)
)

(:action get
:parameters  ()
:precondition (and (= (curf) 1) (> (numf) 0) (< (nume) (cap)))
:effect (and  (decrease (numf) 1) (increase (nume) 1)))

(:action leave
:parameters  ()
:precondition (and  (= (curf) (topf)) (> (nume) 0) )
:effect (and  (decrease (nume) 1) (increase (numt) 1)))

(:action ascend
:parameters  ()
:precondition (and (< (curf) (topf)) (> (nume) 0))
:effect (and  (increase (curf) 1)))

(:action descend
:parameters  ()
:precondition (and (> (curf) 1) (= (nume) 0))
:effect (and  (decrease (curf) 1)))

)