(define(problem pro-Hall-Random)
(:domain Hall-Random)
(:init
(not (dectr))
(dectl)
(not (dectt))
(not (dectb))
(not (visitlt))
(not (visitrt))
(not (visitlb))
(not (visitrb))
( = (disl) 1)
( = (dist) 1)
( = (disb) 3)
( = (startt) 1)
( = (startl) 1)
( = (disr) 0)
)
(:goal(and(visitrt)(visitlt)(visitlb)(visitrb)(=(disl)(startl))(=(dist)(startt))))
)