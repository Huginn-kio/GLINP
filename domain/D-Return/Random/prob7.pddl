(define(problem pro-Diagonal-Return)
(:domain Diagonal-Return)
(:init
(not (visitlt))
(not (visitrt))
(not (visitrb))
( = (disr) 2)
( = (disl) 3)
( = (dist) 4)
( = (disb) 1)
( = (startt) 4)
( = (startl) 3)
)
(:goal(and(visitlt)(visitrt)(visitrb)(=(disl)(startl))(=(dist)(startt))))
)