(define(problem pro-Diagonal-Return)
(:domain Diagonal-Return)
(:init
(not (visitlt))
(not (visitrt))
(not (visitrb))
( = (disr) 2)
( = (disl) 0)
( = (dist) 0)
( = (disb) 1)
( = (startt) 0)
( = (startl) 0)
)
(:goal(and(visitlt)(visitrt)(visitrb)(=(disl)(startl))(=(dist)(startt))))
)