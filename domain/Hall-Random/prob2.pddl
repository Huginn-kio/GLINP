(define(problem pro-Hall-Random)
(:domain Hall-Random)
(:init
(not (dectr))
(not (dectl))
(not (dectt))
(dectb)
(not (visitlt))
(not (visitrt))
(not (visitlb))
(not (visitrb))
( = (disl) 4)
( = (dist) 4)
( = (disb) 4)
( = (startt) 4)
( = (startl) 4)
( = (disr) 0)
)
(:goal(and(visitrt)(visitlt)(visitlb)(visitrb)(=(disl)(startl))(=(dist)(startt))))
)