(define(problem pro-Hall-A)
(:domain Hall-A)
(:init
(not (visitlt))
(not (visitrt))
(not (visitlb))
(not (visitrb))
( = (disl) 2)
( = (dist) 3)
( = (disb) 2)
( = (startt) 3)
( = (startl) 2)
( = (disr) 0)
)
(:goal(and(visitrt)(visitlt)(visitlb)(visitrb)(=(disl)(startl))(=(dist)(startt))))
)