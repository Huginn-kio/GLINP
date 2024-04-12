(define (domain grid1)
  (:requirements :typing :fluents)
  (:predicates
    (gotkey)
    (isopen)
  )

(:functions
    (xagt)
    (yagt)
    (xkey)
    (ykey)
    (xlock)
    (ylock)
    (width)
    (height)
)

(:action mover
:parameters  ()
:precondition (and  (< (xagt) (width)))
:effect (and (increase (xagt) 1)))

(:action movel
:parameters  ()
:precondition (and  (> (xagt) 0))
:effect (and (decrease (xagt) 1)))

(:action moveu
:parameters  ()
:precondition (and  (> (yagt) 0))
:effect (and (decrease (yagt) 1)))

(:action moved
:parameters  ()
:precondition (and  (< (yagt) (height)))
:effect (and (increase (yagt) 1)))

(:action pick
:parameters  ()
:precondition (and  (= (xagt) (xkey)) (= (yagt) (ykey)) (not (gotkey)))
:effect (and (gotkey)))


(:action open
:parameters  ()
:precondition (and  (= (xagt) (xlock)) (= (yagt) (ylock)) (gotkey) (not (isopen)) )
:effect (and  (isopen))))



