(define(problem prob-Delivery)
(:domain Delivery)
(:init
(not (atd))
( = (numd) 2)
( = (cap) 2)
( = (numc) 0)
( = (numt) 0)
)
(:goal(and(atd)(=(numd)0)(=(numt)0)))
)